module Hpie.Env where

import Control.Monad.Reader
import Hpie.Types (HpieError (..), Symbol, Tele, Term)

data Env = Env
  { ctx :: [VEntry],
    bound :: [Symbol]
  }
  deriving (Show)

initEnv :: Env
initEnv = Env {ctx = [], bound = []}

data Closure a = Closure Env a
  deriving (Show)

data Value
  = VPi Value (Closure (Symbol, Term))
  | VLam (Closure (Symbol, Term))
  | VSigma Value (Closure (Symbol, Term))
  | VCons Value Value
  | VU
  | VConstructor (Closure Tele)
  | VData (Closure Tele)
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Symbol
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  deriving (Show)

type Ty = Value

data VEntry
  = VDef Symbol Value
  | VIsA Symbol Ty
  | VDataDef Symbol Value [(Symbol, Value)]
  deriving (Show)

type TcMonad = ReaderT Env (Either HpieError)

runTcMonad :: TcMonad a -> Env -> Either HpieError a
runTcMonad = runReaderT

extendEnv :: VEntry -> TcMonad a -> TcMonad a
extendEnv entry =
  local
    ( \e@Env {ctx = c} ->
        e {ctx = entry : c}
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

searchTy :: Symbol -> TcMonad Ty
searchTy x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go (VIsA symbol ty : es)
      | symbol == x = return ty
      | otherwise = go es
    go (_ : es) = go es

searchV :: Symbol -> TcMonad Value
searchV x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go (VIsA symbol _ : es)
      | symbol == x = return (VNeutral (NVar x))
      | otherwise = go es
    go (VDef symbol v : es)
      | symbol == x = return v
      | otherwise = go es

throwE :: HpieError -> TcMonad a
throwE e = lift (Left e)

close :: a -> TcMonad (Closure a)
close t = do
  e <- getEnv
  return (Closure e t)