module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import qualified Hpie.Norm as Norm
import Hpie.Types

failCheck :: CtxWorker a
failCheck = CtxWorker (\_ -> Left ())

eval :: Term -> CtxWorker Value
eval = toCtxWorker . Norm.eval

reify :: Value -> CtxWorker Term
reify = toCtxWorker . Norm.reify

evalInEnv :: Env Value -> Term -> CtxWorker Value
evalInEnv env t = toCtxWorker (Norm.withEnv env (Norm.eval t))

doSecond :: Value -> CtxWorker Value
doSecond = toCtxWorker . Norm.doSecond

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
infer (App f arg) = do
  fTy <- infer f
  case fTy of
    (VPi _ aT closure) -> do
      _ <- check arg aT
      argV <- eval arg
      doApplyClosure closure argV
    _ -> failCheck
infer (Sigma x a b) = do
  _ <- check a VU
  va <- eval a
  _ <- extendCtx x (IsA va) (check b VU)
  return VU
infer (First p) = do
  pTy <- infer p
  case pTy of
    (VSigma _ aT _) -> return aT
    _ -> failCheck
infer (Second p) = do
  pTy <- infer p
  pV <- eval p
  case pTy of
    (VSigma _ _ closure) -> do
      secondV <- doSecond pV
      doApplyClosure closure secondV
    _ -> failCheck
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
    _ -> failCheck
infer U = return VU
infer _ = failCheck

check :: Term -> Value -> CtxWorker ()
check (Lam x t) fTy = case fTy of
  (VPi _ aT closure) -> do
    tT <- doApplyClosure closure (VNeutral (NVar x))
    extendCtx x (IsA aT) (check t tT)
  _ -> failCheck
check (Cons first second) pTy = case pTy of
  (VSigma _ aT closure) -> do
    _ <- check first aT
    firstV <- eval first
    secondT <- doApplyClosure closure firstV
    check second secondT
  _ -> failCheck
check Zero nTy = case nTy of
  VNat -> return ()
  _ -> failCheck
check (Succ n) nTy = case nTy of
  VNat -> check n VNat
  _ -> failCheck
check other tTy = do
  tTy' <- infer other
  convert tTy tTy'

convert :: Value -> Value -> CtxWorker ()
convert v1 v2 = do
  e1 <- reify v1
  e2 <- reify v2
  case AlphaEq.alphaEq e1 e2 of
    Left () -> failCheck
    Right () -> return ()
