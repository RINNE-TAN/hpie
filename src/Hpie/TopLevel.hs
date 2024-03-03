module Hpie.TopLevel where

import Control.Monad.Reader
import Control.Monad.State (StateT (runStateT), get, put)
import qualified Hpie.CheckTy as CheckTy
import Hpie.Env (Env (..), Ty, VEntry (..), Value)
import qualified Hpie.Env as Env
import qualified Hpie.Norm as Norm
import Hpie.Parser
import Hpie.Types

type TopMonad = StateT Env (Either HpieError)

runTopMonad :: TopMonad a -> Env -> Either HpieError (a, Env)
runTopMonad = runStateT

tc2top :: Env.TcMonad a -> TopMonad a
tc2top tc = do
  env <- get
  lift $ Env.runTcMonad tc env

topLevelMain :: String -> [TopLevelMsg]
topLevelMain s = case runTopMonad (topLevel s) Env.initEnv of
  Left e -> error $ show e
  Right (v, _) -> v

parser :: String -> Parser a -> TopMonad (Input, a)
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

check :: Term -> Value -> TopMonad ()
check term value = tc2top $ CheckTy.check term value

addDef :: VEntry -> TopMonad ()
addDef entry = do
  env@Env {ctx = c} <- get
  put $ env {ctx = entry : c}

runOne :: TopLevel -> TopMonad TopLevelMsg
runOne (IsA x t) = do
  ty <- eval t
  tNorm <- reify ty
  addDef (VIsA x ty)
  return $ AddIsA x tNorm
runOne (Def x e) = do
  ty <- searchTy x
  tyNorm <- reify ty
  check e ty
  eV <- eval e
  eNorm <- reify eV
  addDef (VDef x eV)
  return $ AddDef x eNorm tyNorm

topLevel :: String -> TopMonad [TopLevelMsg]
topLevel input = do
  (_, tops) <- parser input pProg
  foldr
    ( \curWork tailWork -> do
        cur <- runOne curWork
        tails <- tailWork
        return $ cur : tails
    )
    (return [])
    tops
