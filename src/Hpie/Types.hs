module Hpie.Types where

type Symbol = String

freshen :: [Symbol] -> Symbol -> Symbol
freshen = go 0
  where
    go :: Int -> [Symbol] -> Symbol -> Symbol
    go idx bound start =
      let x = start ++ show idx
       in if x `elem` bound
            then go (idx + 1) bound start
            else x

newtype Env val = Env [(Symbol, val)]
  deriving (Show)

instance Functor Env where
  fmap f (Env e) = Env (fmap (\(a, b) -> (a, f b)) e)

initEnv :: Env a
initEnv = Env []

lookV :: Env a -> Symbol -> Either () a
lookV (Env []) _ = Left ()
lookV (Env ((s, v) : e)) k
  | k == s = Right v
  | otherwise = lookV (Env e) k

extend :: Env a -> (Symbol, a) -> Env a
extend (Env e) p = Env (p : e)

data Closure = Closure (Env Value) (Symbol, Term)
  deriving (Show)

data Term
  = Var Symbol -- x
  | Pi Symbol Term Term -- Π(x:A) B
  | Arrow Term Term -- A -> B
  | Lam Symbol Term -- λ(x) t
  | App Term Term -- f arg
  | Sigma Symbol Term Term -- Σ(x:A) D
  | Cons Term Term -- ons l r
  | First Term -- first p
  | Second Term -- second p
  | Nat -- Nat
  | Zero -- Zero
  | Succ Term -- Succ n
  -- ind-nat target mot base step
  -- target : Nat
  -- mot : Nat -> U
  -- base : mot Zero
  -- step : Π(n:Nat) (mot n) -> (mot Succ n)
  | IndNat Term Term Term Term
  | U -- U
  deriving (Show, Eq)

data Value
  = VPi Symbol Value Closure
  | VLam Symbol Closure
  | VSigma Symbol Value Closure
  | VCons Value Value
  | VNat
  | VZero
  | VSucc Value
  | VU
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Symbol
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  | NIndNat Neutral Value Value Value
  deriving (Show)

newtype Worker a = Worker
  { runWorker :: Env Value -> [Symbol] -> a
  }

instance Functor Worker where
  fmap f (Worker n) = Worker (\env bound -> f (n env bound))

instance Applicative Worker where
  pure a = Worker (\_ _ -> a)
  (<*>) (Worker nab) (Worker na) = Worker (\env bound -> nab env bound (na env bound))

instance Monad Worker where
  (>>=) (Worker na) f =
    Worker (\env bound -> runWorker (f (na env bound)) env bound)

data CtxEntry a = Def a a | IsA a
  deriving (Show)

newtype CtxWorker a = CtxWorker
  { runCtxWorker :: Env (CtxEntry Value) -> Either () a
  }

instance Functor CtxWorker where
  fmap f (CtxWorker ckta) = CtxWorker (fmap f . ckta)

instance Applicative CtxWorker where
  pure x = CtxWorker (\_ -> Right x)
  (<*>) (CtxWorker cktab) (CtxWorker ckta) = CtxWorker (\e -> cktab e <*> ckta e)

instance Monad CtxWorker where
  (>>=) (CtxWorker ckta) f =
    CtxWorker
      ( \ctx -> case ckta ctx of
          Left () -> Left ()
          Right r -> runCtxWorker (f r) ctx
      )

toCtxWorker :: Worker a -> CtxWorker a
toCtxWorker (Worker norm) = do
  ctx <- getCtx
  return $ norm (mkEnv ctx) []

mkEnv :: Env (CtxEntry Value) -> Env Value
mkEnv (Env []) = Env []
mkEnv (Env ((s, e) : es)) = Env ((s, v) : nes)
  where
    Env nes = mkEnv (Env es)
    v = case e of
      IsA _ -> VNeutral (NVar s)
      Def value _ -> value

getCtx :: CtxWorker (Env (CtxEntry Value))
getCtx = CtxWorker return

getTy :: CtxEntry Value -> Value
getTy (IsA ty) = ty
getTy (Def _ ty) = ty

extendCtx :: Symbol -> CtxEntry Value -> CtxWorker a -> CtxWorker a
extendCtx s v (CtxWorker ckt) = CtxWorker (\ctx -> ckt (extend ctx (s, v)))

data TopLevel
  = Claim Symbol Term
  | Define Symbol Term
  | CheckSame Term Term Term
  deriving (Show)

data TopLevelMsg
  = AddClaim Symbol Term
  | AddDefine Symbol Term Term
  | IsSame
  | NotSame
  deriving (Show)