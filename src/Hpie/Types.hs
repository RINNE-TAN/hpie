module Hpie.Types where

import Text.Printf (printf)

type Symbol = String

freshen :: [Symbol] -> Symbol -> Symbol
freshen b s =
  if s `notElem` b || s == "_"
    then s
    else go 0 b s
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
  fmap f (Env e) = Env ((\(a, b) -> (a, f b)) <$> e)

initEnv :: Env a
initEnv = Env []

lookV :: Env a -> Symbol -> Either RuntimeError a
lookV (Env []) s = Left $ VarNotFound s
lookV (Env ((s, v) : e)) k
  | k == s = Right v
  | otherwise = lookV (Env e) k

extend :: Env a -> (Symbol, a) -> Env a
extend (Env e) p = Env (p : e)

data Closure = Closure (Env Value) Symbol Term
  deriving (Show)

data Term
  = Var Symbol -- x
  | Pi Symbol Term Term -- Π(x:A) B
  | Arrow Term Term -- A -> B
  | Lam Symbol Term -- λ(x) t
  | App Term Term -- f arg
  | Sigma Symbol Term Term -- Σ(x:A) D
  | Pair Term Term -- Pair A D
  | Cons Term Term -- (l, r)
  | First Term -- First p
  | Second Term -- Second p
  | Trivial -- Trivial
  | Sole -- Sole
  | Absurd -- Absurd
  -- IndAbsurd
  -- target : Absurd
  -- mot : U
  -- -> mot
  | IndAbsurd Term Term
  | Bool -- Bool
  | T -- True
  | F -- False
  -- IndBool
  -- target : Bool
  -- mot : Bool -> U
  -- fBase : mot False
  -- tBase : mot True
  -- -> mot target
  | IndBool Term Term Term Term
  | U -- U

instance Show Term where
  show (Var x) = x
  show (Pi x a b) =
    if x == "_"
      then show (Arrow a b)
      else printf "Π(%s: %s) %s" x (show a) (show b)
  show (Arrow a b) = printf "%s -> %s" (show a) (show b)
  show (Lam x t) = printf "λ(%s) %s" (show x) (show t)
  show (App f arg) = printf "(%s %s)" (show f) (show arg)
  show (Sigma x a b) =
    if x == "_"
      then show (Pair a b)
      else printf "Σ(%s: %s) %s" x (show a) (show b)
  show (Pair a b) = printf "(Pair %s %s)" (show a) (show b)
  show (Cons l r) = printf "(%s, %s)" (show l) (show r)
  show (First p) = printf "(First %s)" (show p)
  show (Second p) = printf "(Second %s)" (show p)
  show Trivial = "Trivial"
  show Sole = "Sole"
  show Absurd = "Absurd"
  show (IndAbsurd target mot) = printf "IndAbsurd %s %s" (show target) (show mot)
  show Bool = "Bool"
  show T = "True"
  show F = "False"
  show (IndBool target mot fBase tBase) =
    printf "IndBool %s %s %s %s" (show target) (show mot) (show fBase) (show tBase)
  show U = "U"

data Value
  = VPi Symbol Value Closure
  | VLam Symbol Closure
  | VSigma Symbol Value Closure
  | VCons Value Value
  | VTrivial
  | VSole
  | VAbsurd
  | VBool
  | VT
  | VF
  | VU
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Symbol
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  | NIndAbsurd Neutral Value
  | NIndBool Neutral Value Value Value
  deriving (Show)

newtype Worker a = Worker
  { runWorker :: Env Value -> [Symbol] -> Either RuntimeError a
  }

instance Functor Worker where
  fmap f (Worker n) = Worker (\env bound -> f <$> n env bound)

instance Applicative Worker where
  pure a = Worker (\_ _ -> Right a)
  (<*>) (Worker nab) (Worker na) = Worker (\env bound -> nab env bound <*> na env bound)

instance Monad Worker where
  (>>=) (Worker na) f =
    Worker
      ( \env bound -> case na env bound of
          Left e -> Left e
          Right r -> runWorker (f r) env bound
      )

data CtxEntry a = Def a a | IsA a
  deriving (Show)

newtype CtxWorker a = CtxWorker
  { runCtxWorker :: Env (CtxEntry Value) -> Either RuntimeError a
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
          Left e -> Left e
          Right r -> runCtxWorker (f r) ctx
      )

toCtxWorker :: Worker a -> CtxWorker a
toCtxWorker (Worker norm) = CtxWorker (\ctx -> norm (mkEnv ctx) [])

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
  | NotSame String
  deriving (Show)

data ParserError
  = EOF
  | Unexpected String String
  | Internal

instance Show ParserError where
  show EOF = "expected input but got eof"
  show (Unexpected expect got) = "expected: " ++ expect ++ " but got: " ++ got
  show Internal = "internal error in parser"

data RuntimeError
  = TypeMissMatch String String
  | AlphaNotEq String String
  | CanNotInfer String
  | VarNotFound String

instance Show RuntimeError where
  show (TypeMissMatch l r) = "type missmatch, expect: " ++ l ++ " but got: " ++ r
  show (AlphaNotEq l r) = l ++ " is not eq with " ++ r
  show (CanNotInfer t) = "can not infer term: " ++ t
  show (VarNotFound v) = "var not found: " ++ v

data TopLevelError
  = RuntimeError RuntimeError
  | ParserError ParserError

instance Show TopLevelError where
  show (RuntimeError re) = "Runtime Error\n" ++ show re
  show (ParserError pe) = "Parser Error\n" ++ show pe