module Hpie.AlphaEq where

import Data.Foldable (traverse_)
import Hpie.Env (TcMonad, throwE)
import Hpie.Types

alphaEq :: Term -> Term -> TcMonad ()
alphaEq t1 t2 = case runAlpha (eq t1 t2) [] [] 0 of
  Left e -> throwE e
  Right _ -> return ()

newtype Alpha a = Alpha
  { runAlpha ::
      [(Symbol, Int)] ->
      [(Symbol, Int)] ->
      Int ->
      Either HpieError a
  }

instance Functor Alpha where
  fmap f (Alpha act) = Alpha (\l r i -> fmap f (act l r i))

instance Applicative Alpha where
  pure x = Alpha (\_ _ _ -> Right x)
  Alpha fun <*> Alpha arg =
    Alpha (\l r i -> fun l r i <*> arg l r i)

with :: Symbol -> Symbol -> Alpha a -> Alpha a
with x y (Alpha act) =
  Alpha (\l r i -> act ((x, i) : l) ((y, i) : r) (i + 1))

no :: Term -> Term -> Alpha ()
no l r = Alpha (\_ _ _ -> Left $ AlphaNotEq (show l) (show r))

yes :: Alpha ()
yes = pure ()

rawEq :: (Eq a, Show a) => a -> a -> Alpha ()
rawEq l r
  | l == r = yes
  | otherwise = Alpha (\_ _ _ -> Left $ AlphaNotEq (show l) (show r))

listEq :: [a] -> [a] -> (a -> a -> Alpha ()) -> Alpha ()
listEq llist rlist f = rawEq (length llist) (length rlist) *> traverse_ (uncurry f) (zip llist rlist)

eq :: Term -> Term -> Alpha ()
eq left right =
  case (left, right) of
    (Var x, Var y) ->
      Alpha
        ( \l r _ -> case (lookup x l, lookup y r) of
            (Nothing, Nothing)
              | x == y -> Right ()
              | otherwise -> Left $ AlphaNotEq x y
            (Just i, Just j)
              | i == j -> Right ()
              | otherwise -> Left $ AlphaNotEq x y
            _ -> Left $ AlphaNotEq x y
        )
    (Pi x1 a1 b1, Pi x2 a2 b2) ->
      eq a1 a2 *> with x1 x2 (eq b1 b2)
    (Arrow a1 b1, Arrow a2 b2) -> eq a1 b1 *> eq a2 b2
    (Lam x1 t1, Lam x2 t2) ->
      with x1 x2 (eq t1 t2)
    (Rec x1 t1, Rec x2 t2) -> with x1 x2 (eq t1 t2)
    (App f1 arg1, App f2 arg2) -> eq f1 f2 *> eq arg1 arg2
    (Sigma x1 a1 b1, Sigma x2 a2 b2) ->
      eq a1 a2 *> with x1 x2 (eq b1 b2)
    (Pair a1 b1, Pair a2 b2) -> eq a1 a2 *> eq b1 b2
    (Prod l1 r1, Prod l2 r2) ->
      eq l1 l2 *> eq r1 r2
    (First p1, First p2) -> eq p1 p2
    (Second p1, Second p2) -> eq p1 p2
    (TyCon x1 args1, TyCon x2 args2) ->
      rawEq x1 x2
        *> listEq args1 args2 eq
    (DataCon x1 args1, DataCon x2 args2) ->
      rawEq x1 x2
        *> listEq args1 args2 eq
    (Match term1 case1, Match term2 case2) ->
      eq term1 term2
        *> listEq
          case1
          case2
          (\(Case pat1 c1) (Case pat2 c2) -> rawEq pat1 pat2 *> eq c1 c2)
    (U, U) -> yes
    (l, r) -> no l r