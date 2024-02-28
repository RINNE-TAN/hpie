module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import Hpie.Env (Entry (..), Neutral (..), TcMonad, Ty, Value (..))
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
  _ <- check a VU
  aV <- Norm.eval a
  _ <- Env.extendEnv x (IsA aV) (check b VU)
  return VU
infer (Arrow a b) = do
  _ <- check a VU
  _ <- check b VU
  return VU
infer (App f arg) = do
  fTy <- infer f
  case fTy of
    (VPi _ aT closure) -> do
      _ <- check arg aT
      argV <- Norm.eval arg
      Norm.doApplyClosure closure argV
    _ -> failCheck "Pi Type" fTy
infer (Sigma x a b) = do
  _ <- check a VU
  va <- Norm.eval a
  _ <- Env.extendEnv x (IsA va) (check b VU)
  return VU
infer (Pair a b) = do
  _ <- check a VU
  _ <- check b VU
  return VU
infer (First p) = do
  pTy <- infer p
  case pTy of
    (VSigma _ aT _) -> return aT
    _ -> failCheck "Sigma Type" pTy
infer (Second p) = do
  pTy <- infer p
  pV <- Norm.eval p
  case pTy of
    (VSigma _ _ closure) -> do
      firstV <- Norm.doFirst pV
      Norm.doApplyClosure closure firstV
    _ -> failCheck "Sigma Type" pTy
infer U = return VU
infer other = Env.throwE $ CanNotInfer (show other)

check :: Term -> Value -> TcMonad ()
check (Lam x t) fTy = case fTy of
  (VPi _ aT closure) -> do
    y <- Norm.fresh x
    tT <- Norm.doApplyClosure closure (VNeutral (NVar y))
    Env.extendEnv y (IsA aT) (check t tT)
  _ -> failCheck "Pi Type" fTy
check (Cons first second) pTy = case pTy of
  (VSigma _ aT closure) -> do
    _ <- check first aT
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
  case AlphaEq.alphaEq e1 e2 of
    Left e -> Env.throwE e
    Right () -> return ()
