module Hpie.Env where

import Control.Monad.Except (ExceptT, MonadError (throwError))
import Control.Monad.Reader
import Hpie.Types (Case, HpieError (..), Symbol, Tele, Term)

data Env = Env
  { ctx :: [VEntry],
    bound :: [Symbol]
  }

instance Show Env where
  show _ = "Env(..)"

initEnv :: Env
initEnv = Env {ctx = [], bound = []}

data Closure a = Closure Env a
  deriving (Show)

data Value
  = VPi Value (Closure (Symbol, Term))
  | VLam (Closure (Symbol, Term))
  | VRec Symbol (Closure Term)
  | VSigma Value (Closure (Symbol, Term))
  | VCons Value Value
  | VU
  | VTyCon Symbol [Value]
  | VDataCon Symbol [Value]
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Symbol
  | NApp Neutral Value
  | NFirst Neutral
  | NSecond Neutral
  | NMatch Neutral [Case]
  deriving (Show)

type Ty = Value

data VEntry
  = VDef Symbol Value
  | VIsA Symbol Ty
  | VTyDef Symbol Tele [(Symbol, Tele)]
  deriving (Show)

type TcMonad = ReaderT Env (ExceptT HpieError IO)

runTcMonad :: TcMonad a -> Env -> ExceptT HpieError IO a
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
    go (_ : es) = go es

searchTyCon :: Symbol -> TcMonad VEntry
searchTyCon x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go (v@(VTyDef symbol _ _) : es)
      | symbol == x = return v
      | otherwise = go es
    go (_ : es) = go es

searchTyConWithDataCon :: Symbol -> Symbol -> TcMonad (Tele, Tele)
searchTyConWithDataCon tySymbol dataSymbol = do
  tyCon <- searchTyCon tySymbol
  case tyCon of
    VTyDef _ teles dataCons -> do
      dataTeles <- go dataCons
      return (teles, dataTeles)
  where
    go [] = throwE (DataConMissMatch tySymbol dataSymbol)
    go ((x, v) : xs)
      | x == dataSymbol = return v
      | otherwise = go xs

throwE :: HpieError -> TcMonad a
throwE = throwError

logInfo :: (Show a) => a -> TcMonad ()
logInfo s = liftIO $ print s

close :: a -> TcMonad (Closure a)
close t = do
  e <- getEnv
  return (Closure e t)