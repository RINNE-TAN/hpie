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

data Term
  = Var Symbol -- x
  | Pi Symbol Term Term -- Π(x:A) B
  | Lam Symbol Term -- λ(x) t
  | App Term Term -- f arg
  | Sigma Symbol Term Term -- Σ(x:A) D
  | Pair Term Term -- (l,r)
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
  | VPair Value Value
  | VNat
  | VZero
  | VSucc Value
  | VU
  | VNeutral Neutral

data Neutral
  = NVar Symbol
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  | NIndNat Neutral Value Value Value

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