module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import qualified Hpie.Norm as Norm
import Hpie.Types

failWithError :: RuntimeError -> CtxWorker a
failWithError re = CtxWorker (\_ -> Left re)

failCheck :: String -> Value -> CtxWorker a
failCheck expected got = do
  gotNorm <- reify got
  failWithError $ TypeMissMatch expected (show gotNorm)

fresh :: Symbol -> CtxWorker Symbol
fresh = toCtxWorker . Norm.fresh

eval :: Term -> CtxWorker Value
eval = toCtxWorker . Norm.eval

reify :: Value -> CtxWorker Term
reify = toCtxWorker . Norm.reify

evalInEnv :: Env Value -> Term -> CtxWorker Value
evalInEnv env t = toCtxWorker (Norm.withEnv env (Norm.eval t))

doFirst :: Value -> CtxWorker Value
doFirst = toCtxWorker . Norm.doFirst

doApply :: Value -> Value -> CtxWorker Value
doApply f arg = toCtxWorker $ Norm.doApply f arg

doApplyClosure :: Closure -> Value -> CtxWorker Value
doApplyClosure c v = toCtxWorker $ Norm.doApplyClosure c v

lookupTy :: Symbol -> CtxWorker Value
lookupTy s =
  CtxWorker
    ( \ctx -> do
        entry <- lookV ctx s
        return $ getTy entry
    )

infer :: Term -> CtxWorker Value
infer (Var x) = lookupTy x
infer (Pi x a b) = do
  _ <- check a VU
  aV <- eval a
  _ <- extendCtx x (IsA aV) (check b VU)
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
      argV <- eval arg
      doApplyClosure closure argV
    _ -> failCheck "Pi Type" fTy
infer (Sigma x a b) = do
  _ <- check a VU
  va <- eval a
  _ <- extendCtx x (IsA va) (check b VU)
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
  pV <- eval p
  case pTy of
    (VSigma _ _ closure) -> do
      firstV <- doFirst pV
      doApplyClosure closure firstV
    _ -> failCheck "Sigma Type" pTy
infer Nat = return VU
infer (IndNat target mot base step) = do
  targetTy <- infer target
  targetV <- eval target
  case targetTy of
    VNat -> do
      motTy <- eval (Pi "x" Nat U)
      _ <- check mot motTy
      motV <- eval mot
      baseTy <- doApply motV VZero
      _ <- check base baseTy
      stepTy <-
        evalInEnv
          (Env [("mot", motV)])
          ( Pi
              "n"
              Nat
              ( Pi
                  "almost"
                  (App (Var "mot") (Var "n"))
                  (App (Var "mot") (Succ (Var "n")))
              )
          )
      _ <- check step stepTy
      doApply motV targetV
    _ -> failCheck "Nat Type" targetTy
infer U = return VU
infer other = failWithError $ CanNotInfer (show other)

check :: Term -> Value -> CtxWorker ()
check (Lam x t) fTy = case fTy of
  (VPi _ aT closure) -> do
    y <- fresh x
    tT <- doApplyClosure closure (VNeutral (NVar y))
    extendCtx y (IsA aT) (check t tT)
  _ -> failCheck "Pi Type" fTy
check (Cons first second) pTy = case pTy of
  (VSigma _ aT closure) -> do
    _ <- check first aT
    firstV <- eval first
    secondT <- doApplyClosure closure firstV
    check second secondT
  _ -> failCheck "Sigma Type" pTy
check Zero nTy = case nTy of
  VNat -> return ()
  _ -> failCheck "Nat Type" nTy
check (Succ n) nTy = case nTy of
  VNat -> check n VNat
  _ -> failCheck "Nat Type" nTy
check other tTy = do
  tTy' <- infer other
  convert tTy tTy'

convert :: Value -> Value -> CtxWorker ()
convert v1 v2 = do
  e1 <- reify v1
  e2 <- reify v2
  case AlphaEq.alphaEq e1 e2 of
    Left e -> failWithError e
    Right () -> return ()
