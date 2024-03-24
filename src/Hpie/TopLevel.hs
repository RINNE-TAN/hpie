module Hpie.TopLevel where

import Control.Monad.Except (ExceptT, runExceptT)
import Control.Monad.Reader
import Control.Monad.State (StateT (runStateT), get, put)
import qualified Hpie.CheckTy as CheckTy
import Hpie.Env (Env (..), Ty, Value)
import qualified Hpie.Env as Env
import qualified Hpie.Norm as Norm
import Hpie.Parser
import Hpie.Types

type TopMonad = StateT Env (ExceptT HpieError IO)

runTopMonad :: TopMonad a -> Env -> IO (Either HpieError (a, Env))
runTopMonad top state = runExceptT (runStateT top state)

tc2top :: Env.TcMonad a -> TopMonad a
tc2top tc = do
  env <- get
  lift $ Env.runTcMonad tc env

topLevelMain :: String -> IO (Either HpieError ((), Env))
topLevelMain s = runTopMonad (topLevel s) Env.initEnv

parser :: String -> Parser a -> TopMonad (a, PState)
parser input pa =
  case runParser pa input of
    Left e -> error $ show e
    Right v -> return v

eval :: Term -> TopMonad Value
eval = tc2top . Norm.eval

reify :: Value -> TopMonad Term
reify = tc2top . Norm.reify

searchTy :: Symbol -> TopMonad Ty
searchTy = tc2top . Env.searchTy

check :: Term -> Term -> TopMonad ()
check term ty = tc2top $ CheckTy.check term ty

tcEntry :: Entry -> TopMonad Entry
tcEntry = tc2top . CheckTy.tcEntry

logInfo :: (Show a) => a -> TopMonad ()
logInfo = tc2top . Env.logInfo

addDef :: Entry -> TopMonad ()
addDef entry = do
  env@Env {ctx = c} <- get
  put $ env {ctx = entry : c}

runOne :: TopLevel -> TopMonad ()
runOne entry = do
  vEntry <- tcEntry entry
  logInfo vEntry
  addDef vEntry

topLevel :: String -> TopMonad ()
topLevel input = do
  (tops, _) <- parser input pProg
  mapM_ runOne tops
