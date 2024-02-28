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

data Term
  = Var Symbol -- x
  | Pi Symbol Term Term -- Π(x:A) B
  | Arrow Term Term -- A -> B
  | Lam Symbol Term -- λ(x) t
  | App Term Term -- f arg
  | Sigma Symbol Term Term -- Σ(x:A) D
  | Pair Term Term -- Pair A D
  | Cons Term Term -- (l, r)
  | First Term -- fst p
  | Second Term -- snd p
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
  show U = "U"

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

data HpieError
  = TypeMissMatch String String
  | AlphaNotEq String String
  | CanNotInfer String
  | VarNotFound String
  deriving (Show)

data ParserError
  = EOF
  | Unexpected String String
  | Internal
  deriving (Show)