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
  = Var Symbol
  | Pi Symbol Term Term
  | Arrow Term Term
  | Lam Symbol Term
  | Rec Symbol Term
  | App Term Term
  | Sigma Symbol Term Term
  | Pair Term Term
  | Prod Term Term
  | First Term
  | Second Term
  | TyCon Symbol [Term]
  | DataCon Symbol [Term]
  | Match Term [Case]
  | U

data Case = Case Pattern Term
  deriving (Show)

data Pattern
  = PatCon Symbol [Pattern]
  | PatVar Symbol
  deriving (Eq, Show)

instance Show Term where
  show (Var x) = x
  show (Pi x a b) =
    if x == "_"
      then show (Arrow a b)
      else printf "Π(%s: %s) %s" x (show a) (show b)
  show (Arrow a b) = printf "%s -> %s" (show a) (show b)
  show (Lam x t) = printf "λ(%s) %s" (show x) (show t)
  show (Rec x t) = printf "@(%s) %s" (show x) (show t)
  show (App f arg) = printf "(%s %s)" (show f) (show arg)
  show (Sigma x a b) =
    if x == "_"
      then show (Pair a b)
      else printf "Σ(%s: %s) %s" x (show a) (show b)
  show (Pair a b) = printf "(Pair %s %s)" (show a) (show b)
  show (Prod l r) = printf "(%s, %s)" (show l) (show r)
  show (First p) = printf "(First %s)" (show p)
  show (Second p) = printf "(Second %s)" (show p)
  show (TyCon symbol args) = printf "%s %s" (show symbol) (show args)
  show (DataCon symbol args) = printf "%s %s" (show symbol) (show args)
  show (Match term cases) = printf "case %s of %s" (show term) (show cases)
  show U = "U"

type TopLevel = Entry

data Entry
  = Def Symbol Term -- [x = a]
  | IsA Symbol Term -- [x : A]
  | TyDef Symbol Tele [DataDef]
  deriving (Show)

data DataDef = DataDef Symbol Tele
  deriving (Show)

type Tele = [Entry] -- [x = a], [x :: a] ...

data HpieError
  = TypeMissMatch String String
  | AlphaNotEq String String
  | CanNotInfer String
  | VarNotFound String
  | DataConMissMatch String String
  | ArgNumMissMatch
  | PatternNotMatch
  deriving (Show)

data ParserError
  = EOF
  | Unexpected String String
  | Internal
  deriving (Show)