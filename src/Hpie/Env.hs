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

type Ty = Term

type TcMonad = ReaderT Env (ExceptT HpieError IO)

runTcMonad :: TcMonad a -> Env -> ExceptT HpieError IO a
runTcMonad = runReaderT

extendEnv :: Entry -> TcMonad a -> TcMonad a
extendEnv entry tc =
  boundEntry entry $
    local
      ( \e@Env {ctx = c} ->
          e {ctx = entry : c}
      )
      tc

boundEntry :: Entry -> TcMonad a -> TcMonad a
boundEntry (IsA x _) = inBound x
boundEntry (Def x _) = inBound x
boundEntry (TyDef x _ _) = inBound x

extendTele :: Tele -> TcMonad a -> TcMonad a
extendTele es tc = foldr extendEnv tc es

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

searchV :: Symbol -> TcMonad Term
searchV x = asks ctx >>= go
  where
    go [] = throwE (VarNotFound x)
    go (IsA symbol _ : es)
      | symbol == x = return (Var x)
      | otherwise = go es
    go (Def symbol v : es)
      | symbol == x = return v
      | otherwise = go es
    go (_ : es) = go es

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
