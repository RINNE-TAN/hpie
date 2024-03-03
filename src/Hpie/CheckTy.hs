module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import Hpie.Env (Neutral (..), TcMonad, Ty, VEntry (..), Value (..))
import qualified Hpie.Env as Env
import qualified Hpie.Norm as Norm
import Hpie.Types

failCheck :: String -> Value -> TcMonad a
failCheck expected got = do
  gotNorm <- Norm.reify got
  Env.throwE $ TypeMissMatch expected (show gotNorm)

infer :: Term -> TcMonad Ty
infer (Var x) = Env.searchTy x
infer (Pi x a b) = do
  check a VU
  aV <- Norm.eval a
  Env.extendEnv (VIsA x aV) (check b VU)
  return VU
infer (Arrow a b) = do
  check a VU
  check b VU
  return VU
infer (App f arg) = do
  fTy <- infer f
  case fTy of
    (VPi aT closure) -> do
      check arg aT
      argV <- Norm.eval arg
      Norm.doApplyClosure closure argV
    _ -> failCheck "Pi Type" fTy
infer (Sigma x a b) = do
  check a VU
  va <- Norm.eval a
  Env.extendEnv (VIsA x va) (check b VU)
  return VU
infer (Pair a b) = do
  check a VU
  check b VU
  return VU
infer (First p) = do
  pTy <- infer p
  case pTy of
    (VSigma aT _) -> return aT
    _ -> failCheck "Sigma Type" pTy
infer (Second p) = do
  pTy <- infer p
  pV <- Norm.eval p
  case pTy of
    (VSigma _ closure) -> do
      firstV <- Norm.doFirst pV
      Norm.doApplyClosure closure firstV
    _ -> failCheck "Sigma Type" pTy
infer U = return VU
infer other = Env.throwE $ CanNotInfer (show other)

check :: Term -> Ty -> TcMonad ()
check (Lam x t) fTy = case fTy of
  (VPi aT closure) -> do
    y <- Norm.fresh x
    tT <- Norm.doApplyClosure closure (VNeutral (NVar y))
    Env.extendEnv (VIsA y aT) (check t tT)
  _ -> failCheck "Pi Type" fTy
check (Cons first second) pTy = case pTy of
  (VSigma aT closure) -> do
    check first aT
    firstV <- Norm.eval first
    secondT <- Norm.doApplyClosure closure firstV
    check second secondT
  _ -> failCheck "Sigma Type" pTy
check other tTy = do
  tTy' <- infer other
  convert tTy tTy'

convert :: Value -> Value -> TcMonad ()
convert v1 v2 = do
  e1 <- Norm.reify v1
  e2 <- Norm.reify v2
  AlphaEq.alphaEq e1 e2

tcEntry :: Entry -> TcMonad VEntry
tcEntry (IsA x a) = do
  check a VU
  aV <- Norm.eval a
  return (VIsA x aV)
tcEntry (Def x a) = do
  xTy <- infer (Var x)
  check a xTy
  aV <- Norm.eval a
  return (VDef x aV)
tcEntry (DataDef symbol tele cs) = do
  tcTele tele
  closure <- Env.close tele
  let checkConDefWithDef conDef =
        Env.extendEnv
          (VDataDef symbol (VData closure) [])
          $ extendTele tele (tcConDef conDef)
  ecs <- mapM checkConDefWithDef cs
  return (VDataDef symbol (VData closure) ecs)

tcConDef :: ConDef -> TcMonad (Symbol, Value)
tcConDef (ConDef symbol tele) = do
  tcTele tele
  closure <- Env.close tele
  return (symbol, VConstructor closure)

tcTele :: Tele -> TcMonad ()
tcTele [] = return ()
tcTele (x : xs) = do
  vEntry <- tcEntry x
  Env.extendEnv vEntry (tcTele xs)

extendTele :: Tele -> TcMonad a -> TcMonad a
extendTele [] tc = tc
extendTele (x : xs) tc = do
  vEntry <- tcEntry x
  Env.extendEnv vEntry (extendTele xs tc)