module Hpie.Norm where

import Hpie.Env (Closure (..), Neutral (..), TcMonad, VEntry (..), Value (..))
import qualified Hpie.Env as Env
import Hpie.Types

fresh :: Symbol -> TcMonad Symbol
fresh x =
  do
    bound <- Env.getBound
    return (freshen bound x)

eval :: Term -> TcMonad Value
eval (Var s) = Env.searchV s
eval (Pi x a b) = VPi <$> eval a <*> Env.close (x, b)
eval (Arrow a b) = VPi <$> eval a <*> Env.close ("_", b)
eval (Lam x t) = VLam <$> Env.close (x, t)
eval (App f arg) = do
  fV <- eval f
  argV <- eval arg
  doApply fV argV
eval (Sigma x a b) = VSigma <$> eval a <*> Env.close (x, b)
eval (Pair a b) = VSigma <$> eval a <*> Env.close ("_", b)
eval (Cons l r) = VCons <$> eval l <*> eval r
eval (First p) = eval p >>= doFirst
eval (Second p) = eval p >>= doSecond
eval U = return VU

doApplyClosure :: Closure (Symbol, Term) -> Value -> TcMonad Value
doApplyClosure (Closure env (s, t)) arg =
  Env.withEnv
    env
    ( Env.extendEnv (VDef s arg) (eval t)
    )

doApply :: Value -> Value -> TcMonad Value
doApply (VLam closure) arg = doApplyClosure closure arg
doApply (VNeutral ne) arg = return $ VNeutral (NApp ne arg)
doApply f arg = error $ "fun is " ++ show f ++ "\n" ++ "arg is " ++ show arg

doFirst :: Value -> TcMonad Value
doFirst (VCons l _) = return l
doFirst (VNeutral ne) = return $ VNeutral (NFirst ne)

doSecond :: Value -> TcMonad Value
doSecond (VCons _ r) = return r
doSecond (VNeutral ne) = return $ VNeutral (NSecond ne)

reifyClosure :: Closure (Symbol, Term) -> TcMonad (Symbol, Term)
reifyClosure closure@(Closure _ (x, _)) = do
  y <- fresh x
  bV <- doApplyClosure closure (VNeutral (NVar y))
  bT <- Env.inBound y (reify bV)
  return (y, bT)

reify :: Value -> TcMonad Term
reify (VPi a closure) = do
  aT <- reify a
  (y, bT) <- reifyClosure closure
  return $ Pi y aT bT
reify (VLam closure) = do
  (y, bT) <- reifyClosure closure
  return $ Lam y bT
reify (VSigma a closure) = do
  aT <- reify a
  (y, bT) <- reifyClosure closure
  return $ Sigma y aT bT
reify (VCons l r) = Cons <$> reify l <*> reify r
reify VU = return U
reify (VNeutral neu) = reifyNeutral neu

reifyNeutral :: Neutral -> TcMonad Term
reifyNeutral (NVar x) = return (Var x)
reifyNeutral (NApp f arg) = App <$> reifyNeutral f <*> reify arg
reifyNeutral (NFirst p) = First <$> reifyNeutral p
reifyNeutral (NSecond p) = Second <$> reifyNeutral p