module Hpie.Norm where

import Control.Monad.Except (catchError, zipWithM)
import Hpie.Env (TcMonad)
import qualified Hpie.Env as Env
import Hpie.Types

fresh :: Symbol -> TcMonad Symbol
fresh x =
  do
    bound <- Env.getBound
    return (freshen bound x)

nbe :: Term -> TcMonad Term
nbe (Var x) = Env.searchV x
nbe (Pi x aT bT) = Pi x <$> nbe aT <*> return bT
nbe (Sigma x aT bT) = Sigma x <$> nbe aT <*> return bT
nbe (Arrow aT bT) = nbe (Pi "_" aT bT)
nbe (Pair aT bT) = nbe (Sigma "_" aT bT)
nbe (App f arg) = do
  fNorm <- nbe f
  argNorm <- nbe arg
  case fNorm of
    Lam x body -> doSubst (x, argNorm) body >>= nbe
    _ -> return (App fNorm argNorm)
nbe (Prod l r) = Prod <$> nbe l <*> nbe r
nbe (First p) = do
  pNorm <- nbe p
  case pNorm of
    Prod l _ -> return l
    _ -> return (First pNorm)
nbe (Second p) = do
  pNorm <- nbe p
  case pNorm of
    Prod _ r -> return r
    _ -> return (Second pNorm)
nbe (DataCon name args) = DataCon name <$> mapM nbe args
nbe (TyCon name args) = TyCon name <$> mapM nbe args
nbe (Match term cases) = do
  termNorm <- nbe term
  case termNorm of
    v@(DataCon _ _) ->
      do
        let go ((Case pt body) : cs) =
              ( do
                  substs <- extendWithPattern v pt
                  doSubsts substs body >>= nbe
              )
                `catchError` (\_ -> go cs)
            go [] = Env.throwE PatternNotMatch
        go cases
    _ -> return (Match termNorm cases)
nbe U = return U
nbe TODO = return TODO
nbe other = return other

extendWithPattern :: Term -> Pattern -> TcMonad Tele
extendWithPattern vNorm (PatVar x) = return [Def x vNorm]
extendWithPattern (DataCon dataSymbol args) (PatCon patSymbol pats)
  | dataSymbol == patSymbol && length args == length pats =
      concat <$> zipWithM extendWithPattern args pats
  | otherwise = Env.throwE PatternNotMatch

doSubst :: (Symbol, Term) -> Term -> TcMonad Term
doSubst (x, t) (Var y) | x == y = return t
doSubst (x, _) (Var y) | x /= y = return (Var y)
doSubst (x, t) (Pi y aT bT) | x /= y = Pi y <$> doSubst (x, t) aT <*> doSubst (x, t) bT
doSubst (x, t) (Pi y aT bT) | x == y = Pi y <$> doSubst (x, t) aT <*> return bT
doSubst subst (Arrow aT bT) = doSubst subst (Pi "_" aT bT)
doSubst (x, _) (Lam y body) | x == y = return (Lam y body)
doSubst (x, t) (Lam y body) | x /= y = Lam y <$> doSubst (x, t) body
doSubst subst (App f arg) = App <$> doSubst subst f <*> doSubst subst arg
doSubst (x, t) (Sigma y aT bT) | x /= y = Sigma y <$> doSubst (x, t) aT <*> doSubst (x, t) bT
doSubst (x, t) (Sigma y aT bT) | x == y = Sigma y <$> doSubst (x, t) aT <*> return bT
doSubst subst (Pair aT bT) = doSubst subst (Sigma "_" aT bT)
doSubst subst (Prod l r) = Prod <$> doSubst subst l <*> doSubst subst r
doSubst subst (First p) = First <$> doSubst subst p
doSubst subst (Second p) = Second <$> doSubst subst p
doSubst subst (TyCon name args) = TyCon name <$> mapM (doSubst subst) args
doSubst subst (DataCon name args) = DataCon name <$> mapM (doSubst subst) args
doSubst subst (Match t cases) = Match <$> doSubst subst t <*> mapM (doSubstCase subst) cases
doSubst _ U = return U
doSubst _ TODO = return TODO

doSubstCase :: (Symbol, Term) -> Case -> TcMonad Case
doSubstCase subst (Case pt term) = Case pt <$> doSubst subst term

doSubsts :: Tele -> Term -> TcMonad Term
doSubsts [] term = return term
doSubsts ((Def x t) : substs) term = doSubst (x, t) term >>= doSubsts substs
doSubsts (_ : substs) term = doSubsts substs term