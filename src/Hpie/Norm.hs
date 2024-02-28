module Hpie.Norm where

import Hpie.Env (Closure (..), Entry (..), Neutral (..), TcMonad, Value (..))
import qualified Hpie.Env as Env
import Hpie.Types

fresh :: Symbol -> TcMonad Symbol
fresh x =
  do
    bound <- Env.getBound
    return (freshen bound x)

close :: Symbol -> Term -> TcMonad Closure
close s t = do
  e <- Env.getEnv
  return (Closure e s t)

eval :: Term -> TcMonad Value
eval (Var s) = Env.searchV s
eval (Pi x a b) = VPi x <$> eval a <*> close x b
eval (Arrow a b) = VPi "_" <$> eval a <*> close "_" b
eval (Lam x t) = VLam x <$> close x t
eval (App f arg) = do
  fV <- eval f
  argV <- eval arg
  doApply fV argV
eval (Sigma x a b) = VSigma x <$> eval a <*> close x b
eval (Pair a b) = VSigma "_" <$> eval a <*> close "_" b
eval (Cons l r) = VCons <$> eval l <*> eval r
eval (First p) = eval p >>= doFirst
eval (Second p) = eval p >>= doSecond
eval U = return VU

doApplyClosure :: Closure -> Value -> TcMonad Value
doApplyClosure (Closure env s t) arg =
  Env.withEnv
    env
    ( Env.extendEnv s (Def arg) (eval t)
    )

doApply :: Value -> Value -> TcMonad Value
doApply (VLam _ closure) arg = doApplyClosure closure arg
doApply (VNeutral ne) arg = return $ VNeutral (NApp ne arg)
doApply f arg = error $ "fun is " ++ show f ++ "\n" ++ "arg is " ++ show arg

doFirst :: Value -> TcMonad Value
doFirst (VCons l _) = return l
doFirst (VNeutral ne) = return $ VNeutral (NFirst ne)

doSecond :: Value -> TcMonad Value
doSecond (VCons _ r) = return r
doSecond (VNeutral ne) = return $ VNeutral (NSecond ne)

reifyClosure :: Symbol -> Closure -> TcMonad (Symbol, Term)
reifyClosure x closure = do
  y <- fresh x
  bV <- doApplyClosure closure (VNeutral (NVar y))
  bT <- Env.inBound y (reify bV)
  return (y, bT)

reify :: Value -> TcMonad Term
reify (VPi x a closure) = do
  aT <- reify a
  (y, bT) <- reifyClosure x closure
  return $ Pi y aT bT
reify (VLam x closure) = do
  (y, bT) <- reifyClosure x closure
  return $ Lam y bT
reify (VSigma x a closure) = do
  aT <- reify a
  (y, bT) <- reifyClosure x closure
  return $ Sigma y aT bT
reify (VCons l r) = Cons <$> reify l <*> reify r
reify VU = return U
reify (VNeutral neu) = reifyNeutral neu

reifyNeutral :: Neutral -> TcMonad Term
reifyNeutral (NVar x) = return (Var x)
reifyNeutral (NApp f arg) = App <$> reifyNeutral f <*> reify arg
reifyNeutral (NFirst p) = First <$> reifyNeutral p
reifyNeutral (NSecond p) = Second <$> reifyNeutral p