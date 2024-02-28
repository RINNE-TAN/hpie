module Hpie.Env where

import Control.Monad.Reader
import Hpie.Types (HpieError (..), Symbol, Term)

data Env = Env
  { ctx :: [(Symbol, Entry)],
    bound :: [Symbol]
  }
  deriving (Show)

initEnv :: Env
initEnv = Env {ctx = [], bound = []}

data Closure = Closure Env Symbol Term
  deriving (Show)

data Value
  = VPi Symbol Value Closure
  | VLam Symbol Closure
  | VSigma Symbol Value Closure
  | VCons Value Value
  | VU
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Symbol
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  deriving (Show)

type Ty = Value

data Entry
  = Def Value
  | IsA Ty
  deriving (Show)

type TcMonad = ReaderT Env (Either HpieError)

runTcMonad :: TcMonad a -> Env -> Either HpieError a
runTcMonad = runReaderT

extendEnv :: Symbol -> Entry -> TcMonad a -> TcMonad a
extendEnv symbol entry =
  local
    ( \e@Env {ctx = c} ->
        e {ctx = (symbol, entry) : c}
    )

withEnv :: Env -> TcMonad a -> TcMonad a
withEnv e = local (const e)

getEnv :: TcMonad Env
getEnv = ask

inBound :: Symbol -> TcMonad a -> TcMonad a
inBound x =
  local
    ( \e@Env {bound = b} ->
        e {bound = x : b}
    )

getBound :: TcMonad [Symbol]
getBound = asks bound

search :: Symbol -> TcMonad Entry
search x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go ((symbol, entry) : es)
      | symbol == x = return entry
      | otherwise = go es

searchTy :: Symbol -> TcMonad Ty
searchTy x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go ((symbol, IsA ty) : es)
      | symbol == x = return ty
      | otherwise = go es
    go (_ : es) = go es

searchV :: Symbol -> TcMonad Value
searchV x = f <$> search x
  where
    f (Def v) = v
    f (IsA _) = VNeutral (NVar x)

throwE :: HpieError -> TcMonad a
throwE e = lift (Left e)
