module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import qualified Hpie.Norm as Norm
import Hpie.Types

data CtxEntry a = Def a a | IsA a

newtype CheckTy a = CheckTy
  { runCheck :: Env (CtxEntry Value) -> Either () a
  }

instance Functor CheckTy where
  fmap f (CheckTy ckta) = CheckTy (fmap f . ckta)

instance Applicative CheckTy where
  pure x = CheckTy (\_ -> Right x)
  (<*>) (CheckTy cktab) (CheckTy ckta) = CheckTy (\e -> cktab e <*> ckta e)

instance Monad CheckTy where
  (>>=) (CheckTy ckta) f =
    CheckTy
      ( \ctx -> case ckta ctx of
          Left () -> Left ()
          Right r -> runCheck (f r) ctx
      )

failCheck :: CheckTy a
failCheck = CheckTy (\_ -> Left ())

getTy :: CtxEntry Value -> Value
getTy (IsA ty) = ty
getTy (Def _ ty) = ty

mkEnv :: Env (CtxEntry Value) -> Env Value
mkEnv (Env []) = Env []
mkEnv (Env ((s, e) : es)) = Env ((s, v) : nes)
  where
    Env nes = mkEnv (Env es)
    v = case e of
      IsA _ -> VNeutral (NVar s)
      Def value _ -> value

getCtx :: CheckTy (Env (CtxEntry Value))
getCtx = CheckTy return

extendCtx :: Symbol -> Value -> CheckTy a -> CheckTy a
extendCtx s ty (CheckTy ckt) = CheckTy (\ctx -> ckt (extend ctx (s, IsA ty)))

runNorm :: Worker a -> CheckTy a
runNorm (Worker norm) = do
  ctx <- getCtx
  return $ norm (mkEnv ctx) []

eval :: Term -> CheckTy Value
eval = runNorm . Norm.eval

reify :: Value -> CheckTy Term
reify = runNorm . Norm.reify

evalInEnv :: Env Value -> Term -> CheckTy Value
evalInEnv env t = runNorm (Norm.withEnv env (Norm.eval t))

doSecond :: Value -> CheckTy Value
doSecond = runNorm . Norm.doSecond

doApply :: Value -> Value -> CheckTy Value
doApply f arg = runNorm $ Norm.doApply f arg

doApplyClosure :: Closure -> Value -> CheckTy Value
doApplyClosure c v = runNorm $ Norm.doApplyClosure c v

lookupTy :: Symbol -> CheckTy Value
lookupTy s =
  CheckTy
    ( \ctx -> do
        entry <- lookV ctx s
        return $ getTy entry
    )

infer :: Term -> CheckTy Value
infer (Var x) = lookupTy x
infer (Pi x a b) = do
  _ <- check a VU
  aV <- eval a
  _ <- extendCtx x aV (check b VU)
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
  _ <- extendCtx x va (check b VU)
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
          (Env [("mot", motTy)])
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

check :: Term -> Value -> CheckTy ()
check (Lam x t) fTy = case fTy of
  (VPi _ aT closure) -> do
    tT <- doApplyClosure closure (VNeutral (NVar x))
    extendCtx x aT (check t tT)
  _ -> failCheck
check (Pair first second) pTy = case pTy of
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

convert :: Value -> Value -> CheckTy ()
convert v1 v2 = do
  e1 <- reify v1
  e2 <- reify v2
  case AlphaEq.alphaEq e1 e2 of
    Left () -> failCheck
    Right () -> return ()
