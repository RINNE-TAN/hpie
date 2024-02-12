module Hpie.Norm where

import Hpie.Types

getEnv :: Worker (Env Value)
getEnv = Worker (\e _ -> Right e)

getBound :: Worker [Symbol]
getBound = Worker (\_ bound -> Right bound)

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
var s = Worker (\env _ -> lookV env s)

close :: Symbol -> Term -> Worker Closure
close s t = do
  e <- getEnv
  return $ Closure e s t

eval :: Term -> Worker Value
eval (Var s) = var s
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
eval Trivial = return VTrivial
eval Sole = return VSole
eval Absurd = return VAbsurd
eval (IndAbsurd target mot) = do
  targetV <- eval target
  motV <- eval mot
  doIndAbsurd targetV motV
eval Bool = return VBool
eval T = return VT
eval F = return VF
eval (IndBool target mot fBase tBase) = do
  targetV <- eval target
  motV <- eval mot
  fBaseV <- eval fBase
  tBaseV <- eval tBase
  doIndBool targetV motV fBaseV tBaseV
eval U = return VU

doApplyClosure :: Closure -> Value -> Worker Value
doApplyClosure (Closure env s t) arg = withEnv (extend env (s, arg)) (eval t)

doApply :: Value -> Value -> Worker Value
doApply (VLam _ closure) arg = doApplyClosure closure arg
doApply (VNeutral ne) arg = return $ VNeutral (NApp ne arg)
doApply f arg = error $ "fun is " ++ show f ++ "\n" ++ "arg is " ++ show arg

doFirst :: Value -> Worker Value
doFirst (VCons l _) = return l
doFirst (VNeutral ne) = return $ VNeutral (NFirst ne)

doSecond :: Value -> Worker Value
doSecond (VCons _ r) = return r
doSecond (VNeutral ne) = return $ VNeutral (NSecond ne)

doIndAbsurd :: Value -> Value -> Worker Value
doIndAbsurd (VNeutral ne) mot = return $ VNeutral (NIndAbsurd ne mot)

doIndBool :: Value -> Value -> Value -> Value -> Worker Value
doIndBool VT _ _ tBase = return tBase
doIndBool VF _ fbase _ = return fbase
doIndBool (VNeutral ne) mot fBase tBase = return $ VNeutral (NIndBool ne mot fBase tBase)

reifyClosure :: Symbol -> Closure -> Worker (Symbol, Term)
reifyClosure x closure = do
  y <- fresh x
  bV <- doApplyClosure closure (VNeutral (NVar y))
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
reify (VCons l r) = Cons <$> reify l <*> reify r
reify VTrivial = return Trivial
reify VSole = return Sole
reify VAbsurd = return Absurd
reify VBool = return Bool
reify VT = return T
reify VF = return F
reify VU = return U
reify (VNeutral neu) = reifyNeutral neu

reifyNeutral :: Neutral -> Worker Term
reifyNeutral (NVar x) = return (Var x)
reifyNeutral (NApp f arg) = App <$> reifyNeutral f <*> reify arg
reifyNeutral (NFirst p) = First <$> reifyNeutral p
reifyNeutral (NSecond p) = Second <$> reifyNeutral p
reifyNeutral (NIndAbsurd target mot) =
  IndAbsurd <$> reifyNeutral target <*> reify mot
reifyNeutral (NIndBool target mot fBase tBase) =
  IndBool <$> reifyNeutral target <*> reify mot <*> reify fBase <*> reify tBase