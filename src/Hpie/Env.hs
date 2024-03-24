module Hpie.Env where

import Control.Monad.Except (ExceptT, MonadError (throwError))
import Control.Monad.Reader
import Hpie.Types

data Env = Env
  { ctx :: [Entry],
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

type Ty = Term

type TcMonad = ReaderT Env (ExceptT HpieError IO)

runTcMonad :: TcMonad a -> Env -> ExceptT HpieError IO a
runTcMonad = runReaderT

extendEnv :: Entry -> TcMonad a -> TcMonad a
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
    go (IsA symbol ty : es)
      | symbol == x = return ty
      | otherwise = go es
    go (_ : es) = go es

searchTyCon :: Symbol -> TcMonad Entry
searchTyCon x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go (v@(TyDef symbol _ _) : es)
      | symbol == x = return v
      | otherwise = go es
    go (_ : es) = go es

searchTyConWithDataCon :: Symbol -> Symbol -> TcMonad (Tele, Tele)
searchTyConWithDataCon tySymbol dataSymbol = do
  tyCon <- searchTyCon tySymbol
  case tyCon of
    TyDef _ teles dataCons -> do
      dataTeles <- go dataCons
      return (teles, dataTeles)
  where
    go [] = throwE (DataConMissMatch tySymbol dataSymbol)
    go ((DataDef x v) : xs)
      | x == dataSymbol = return v
      | otherwise = go xs

throwE :: HpieError -> TcMonad a
throwE = throwError

logInfo :: (Show a) => a -> TcMonad ()
logInfo s = liftIO $ print s

printEnv :: TcMonad ()
printEnv = do
  env <- asks ctx
  liftIO $
    do
      print "-------------Env-------------"
      mapM_ print env
      print "-----------------------------"

close :: a -> TcMonad (Closure a)
close t = do
  e <- getEnv
  return (Closure e t)