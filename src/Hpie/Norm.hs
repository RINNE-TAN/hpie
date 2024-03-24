module Hpie.Norm where

import Control.Monad.Except (catchError)
import Control.Monad.Reader
import Hpie.Env (Closure (..), Neutral (..), TcMonad, Value (..))
import qualified Hpie.Env as Env
import Hpie.Types

fresh :: Symbol -> TcMonad Symbol
fresh x =
  do
    bound <- Env.getBound
    return (freshen bound x)

searchV :: Symbol -> TcMonad Value
searchV x = asks Env.ctx >>= go
  where
    go [] = Env.throwE (VarNotFound x)
    go (IsA symbol _ : es)
      | symbol == x = return (VNeutral (NVar x))
      | otherwise = go es
    go (Def symbol v : es)
      | symbol == x = eval v
      | otherwise = go es
    go (_ : es) = go es

eval :: Term -> TcMonad Value
eval (Var s) = searchV s
eval (Pi x a b) = VPi <$> eval a <*> Env.close (x, b)
eval (Arrow a b) = VPi <$> eval a <*> Env.close ("_", b)
eval (Lam x t) = VLam <$> Env.close (x, t)
eval (App f arg) = do
  fV <- eval f
  argV <- eval arg
  doApply fV argV
eval (Sigma x a b) = VSigma <$> eval a <*> Env.close (x, b)
eval (Pair a b) = VSigma <$> eval a <*> Env.close ("_", b)
eval (Prod l r) = VCons <$> eval l <*> eval r
eval (First p) = eval p >>= doFirst
eval (Second p) = eval p >>= doSecond
eval (TyCon symbol args) = VTyCon symbol <$> mapM eval args
eval (DataCon symbol args) = VDataCon symbol <$> mapM eval args
eval (Match term cases) = do
  termV <- eval term
  doApplyMatch termV cases
eval U = return VU

doApplyMatch :: Value -> [Case] -> TcMonad Value
doApplyMatch (VNeutral ne) cases = return $ VNeutral (NMatch ne cases)
doApplyMatch v@(VDataCon _ _) cases = go cases
  where
    go ((Case pt body) : cs) =
      ( do
          extendWithPattern v pt (eval body)
      )
        `catchError` (\_ -> go cs)
    go [] = Env.throwE PatternNotMatch

extendWithPattern :: Value -> Pattern -> TcMonad a -> TcMonad a
extendWithPattern v (PatVar x) tc = do
  vNorm <- reify v
  Env.extendEnv (Def x vNorm) tc
extendWithPattern (VDataCon dataSymbol args) (PatCon patSymbol pats) tc
  | dataSymbol == patSymbol && length args == length pats =
      foldr (\(arg, pat) work -> extendWithPattern arg pat work) tc (zip args pats)
  | otherwise = Env.throwE PatternNotMatch

doApply :: Value -> Value -> TcMonad Value
doApply (VLam (Closure env (s, t))) arg = do
  argNorm <- reify arg
  Env.withEnv
    env
    ( Env.extendEnv (Def s argNorm) (eval t)
    )
doApply (VNeutral ne) arg = return $ VNeutral (NApp ne arg)
doApply f arg = error $ "fun is " ++ show f ++ "\n" ++ "arg is " ++ show arg

doFirst :: Value -> TcMonad Value
doFirst (VCons l _) = return l
doFirst (VNeutral ne) = return $ VNeutral (NFirst ne)

doSecond :: Value -> TcMonad Value
doSecond (VCons _ r) = return r
doSecond (VNeutral ne) = return $ VNeutral (NSecond ne)

reifyClosure :: Closure (Symbol, Term) -> TcMonad (Symbol, Term)
reifyClosure (Closure _ (x, term)) = do
  y <- fresh x
  Env.extendEnv
    (IsA y TopTy)
    ( do
        bT <- Env.inBound y (nbe term)
        return (y, bT)
    )

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
reify (VCons l r) = Prod <$> reify l <*> reify r
reify (VTyCon symbol args) = TyCon symbol <$> mapM reify args
reify (VDataCon symbol args) = DataCon symbol <$> mapM reify args
reify VU = return U
reify (VNeutral neu) = reifyNeutral neu

reifyNeutral :: Neutral -> TcMonad Term
reifyNeutral (NVar x) = return (Var x)
reifyNeutral (NApp f arg) = App <$> reifyNeutral f <*> reify arg
reifyNeutral (NFirst p) = First <$> reifyNeutral p
reifyNeutral (NSecond p) = Second <$> reifyNeutral p
reifyNeutral (NMatch term cases) = do
  termN <- reifyNeutral term
  return $ Match termN cases

nbe :: Term -> TcMonad Term
nbe term = eval term >>= reify

doSubst :: (Symbol, Term) -> Term -> TcMonad Term
doSubst (x, t) body = Env.extendEnv (Def x t) (nbe body)