module Hpie.Norm where

import Hpie.Types

getEnv :: Worker (Env Value)
getEnv = Worker const

getBound :: Worker [Symbol]
getBound = Worker (\_ bound -> bound)

inBound :: Symbol -> Worker a -> Worker a
inBound x (Worker act) =
  Worker (\env bound -> act env (x : bound))

fresh :: Symbol -> Worker Symbol
fresh x =
  do
    bound <- getBound
    return (freshen bound x)

withEnv :: Env Value -> Worker Value -> Worker Value
withEnv e (Worker n) = Worker (\_ -> n e)

var :: Symbol -> Worker Value
var s =
  Worker
    ( \env _ -> case lookV env s of
        Left () -> undefined
        Right v -> v
    )

close :: (Symbol, Term) -> Worker Closure
close p = do
  e <- getEnv
  return $ Closure e p

eval :: Term -> Worker Value
eval (Var s) = var s
eval (Pi x a b) = VPi x <$> eval a <*> close (x, b)
eval (Lam x t) = VLam x <$> close (x, t)
eval (App f arg) = do
  fV <- eval f
  argV <- eval arg
  doApply fV argV
eval (Sigma x a b) = VSigma x <$> eval a <*> close (x, b)
eval (Pair l r) = VPair <$> eval l <*> eval r
eval (First p) = eval p >>= doFirst
eval (Second p) = eval p >>= doSecond
eval Nat = return VNat
eval Zero = return VZero
eval (Succ n) = VSucc <$> eval n
eval (IndNat target mot base step) = do
  targetV <- eval target
  motV <- eval mot
  baseV <- eval base
  stepV <- eval step
  doIndNat targetV motV baseV stepV
eval U = return VU

doApplyClosure :: Closure -> Value -> Worker Value
doApplyClosure (Closure env (s, t)) arg = withEnv (extend env (s, arg)) (eval t)

doApply :: Value -> Value -> Worker Value
doApply (VLam _ closure) arg = doApplyClosure closure arg
doApply (VNeutral ne) arg = return $ VNeutral (NApp ne arg)

doIndNat :: Value -> Value -> Value -> Value -> Worker Value
doIndNat VZero _ base _ = return base
doIndNat (VSucc n) mot base step = do
  stepV <- doIndNat n mot base step
  applyN <- doApply step n
  doApply applyN stepV
doIndNat (VNeutral ne) mot base step =
  return $ VNeutral (NIndNat ne mot base step)

doFirst :: Value -> Worker Value
doFirst (VPair l _) = return l
doFirst (VNeutral ne) = return $ VNeutral (NFirst ne)

doSecond :: Value -> Worker Value
doSecond (VPair _ r) = return r
doSecond (VNeutral ne) = return $ VNeutral (NSecond ne)

reifyClosure :: Symbol -> Closure -> Worker (Symbol, Term)
reifyClosure x closure = do
  y <- fresh x
  let yVal = VNeutral (NVar y)
  bV <- doApplyClosure closure yVal
  bT <- inBound y (reify bV)
  return (y, bT)

reify :: Value -> Worker Term
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
reify (VPair l r) = Pair <$> reify l <*> reify r
reify VNat = return Nat
reify VZero = return Zero
reify (VSucc n) = Succ <$> reify n
reify VU = return U
reify (VNeutral neu) = reifyNeutral neu

reifyNeutral :: Neutral -> Worker Term
reifyNeutral (NVar x) = return (Var x)
reifyNeutral (NApp f arg) = App <$> reifyNeutral f <*> reify arg
reifyNeutral (NFirst p) = First <$> reifyNeutral p
reifyNeutral (NSecond p) = Second <$> reifyNeutral p
reifyNeutral (NIndNat target mot base step) =
  IndNat
    <$> reifyNeutral target
    <*> reify mot
    <*> reify base
    <*> reify step