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
infer Trivial = return VU
infer Absurd = return VU
infer (IndAbsurd target mot) = do
  _ <- check target VAbsurd
  _ <- check mot VU
  eval mot
infer Bool = return VU
infer (IndBool target mot fBase tBase) = do
  _ <- check target VBool
  targetV <- eval target
  motTy <- eval (Pi "b" Bool U)
  _ <- check mot motTy
  motV <- eval mot
  fBaseTy <- doApply motV VF
  _ <- check fBase fBaseTy
  tBaseTy <- doApply motV VT
  _ <- check tBase tBaseTy
  doApply motV targetV
infer (IndW target mot c) = do
  wTy <- infer target
  case wTy of
    VW sTy pTy -> do
      targetV <- eval target
      motTy <-
        evalInEnv
          (Env [("WSP", wTy)])
          (Arrow (Var "WSP") U)
      _ <- check mot motTy
      motV <- eval mot
      cTy <-
        evalInEnv
          (Env [("S", sTy), ("P", pTy), ("WSP", wTy), ("mot", motV)])
          ( Pi
              "s"
              (Var "S") -- Π(s:S)
              ( Pi
                  "f"
                  ( Arrow
                      (App (Var "P") (Var "s"))
                      (Var "WSP")
                  ) -- Π(f:P s -> W S P)
                  ( Arrow -- ->
                      ( Pi
                          "p"
                          (App (Var "P") (Var "s"))
                          ( App
                              (Var "mot")
                              (App (Var "f") (Var "p"))
                          )
                      ) -- Π(p : P s) mot(f p)
                      ( App
                          (Var "mot")
                          (Sup (Var "s") (Var "f"))
                      ) -- mot (Sup s f)
                  )
              )
          )
      check c cTy
      doApply motV targetV
    _ -> failCheck "W Type" wTy
infer (W s p) = do
  _ <- check s VU
  sV <- eval s
  pTy <-
    evalInEnv
      (Env [("S", sV)])
      (Arrow (Var "S") U)
  _ <- check p pTy
  return VU
infer (Either l r) = do
  _ <- check l VU
  _ <- check r VU
  return VU
infer (IndEither target mot onLeft onRight) = do
  eTy <- infer target
  case eTy of
    (VEither lTy rTy) -> do
      targetV <- eval target
      motTy <-
        evalInEnv
          (Env [("eTy", eTy)])
          (Arrow (Var "eTy") U)
      _ <- check mot motTy
      motV <- eval mot
      onLeftTy <-
        evalInEnv
          (Env [("L", lTy), ("mot", motV)])
          ( Pi
              "l"
              (Var "L")
              (App (Var "mot") (Inl (Var "l")))
          )
      _ <- check onLeft onLeftTy
      onRightTy <-
        evalInEnv
          (Env [("R", rTy), ("mot", motV)])
          ( Pi
              "r"
              (Var "R")
              (App (Var "mot") (Inr (Var "r")))
          )
      _ <- check onRight onRightTy
      doApply motV targetV
    _ -> failCheck "Either Type" eTy
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
check Sole tTy = case tTy of
  VTrivial -> return ()
  _ -> failCheck "Trivial Type" tTy
check T bTy = case bTy of
  VBool -> return ()
  _ -> failCheck "Bool Type" bTy
check F bTy = case bTy of
  VBool -> return ()
  _ -> failCheck "Bool Type" bTy
check (Sup s f) wTy = case wTy of
  (VW sTy pTy) -> do
    _ <- check s sTy
    sV <- eval s
    fTy <-
      evalInEnv
        (Env [("P", pTy), ("s", sV), ("WSP", wTy)])
        ( Arrow
            (App (Var "P") (Var "s"))
            (Var "WSP")
        )
    check f fTy
  _ -> failCheck "Sup Type" wTy
check (Inl l) eTy = case eTy of
  (VEither lTy _) -> check l lTy
  _ -> failCheck "Either Type" eTy
check (Inr r) eTy = case eTy of
  (VEither _ rTy) -> check r rTy
  _ -> failCheck "Either Type" eTy
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
