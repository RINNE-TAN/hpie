module Hpie.AlphaEq where

import Hpie.Types

alphaEq :: Term -> Term -> Either RuntimeError ()
alphaEq t1 t2 = runAlpha (eq t1 t2) [] [] 0

newtype Alpha a = Alpha
  { runAlpha ::
      [(Symbol, Int)] ->
      [(Symbol, Int)] ->
      Int ->
      Either RuntimeError a
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
    (App f1 arg1, App f2 arg2) -> eq f1 f2 *> eq arg1 arg2
    (Sigma x1 a1 b1, Sigma x2 a2 b2) ->
      eq a1 a2 *> with x1 x2 (eq b1 b2)
    (Pair a1 b1, Pair a2 b2) -> eq a1 a2 *> eq b1 b2
    (Cons l1 r1, Cons l2 r2) ->
      eq l1 l2 *> eq r1 r2
    (First p1, First p2) -> eq p1 p2
    (Second p1, Second p2) -> eq p1 p2
    (Trivial, Trivial) -> yes
    (Sole, Sole) -> yes
    (Absurd, Absurd) -> yes
    (IndAbsurd target1 mot1, IndAbsurd target2 mot2) ->
      eq target1 target2 *> eq mot1 mot2
    (Bool, Bool) -> yes
    (T, T) -> yes
    (F, F) -> yes
    (IndBool target1 mot1 fBase1 tBase1, IndBool target2 mot2 fBase2 tBase2) ->
      eq target1 target2 *> eq mot1 mot2 *> eq fBase1 fBase2 *> eq tBase1 tBase2
    (W s1 p1, W s2 p2) -> eq s1 s2 *> eq p1 p2
    (Sup s1 f1, Sup s2 f2) -> eq s1 s2 *> eq f1 f2
    (IndW target1 mot1 c1, IndW target2 mot2 c2) ->
      eq target1 target2 *> eq mot1 mot2 *> eq c1 c2
    (Either l1 r1, Either l2 r2) -> eq l1 l2 *> eq r1 r2
    (Inl l1, Inl l2) -> eq l1 l2
    (Inr r1, Inr r2) -> eq r1 r2
    (IndEither target1 mot1 onLeft1 onRight1, IndEither target2 mot2 onLeft2 onRight2) ->
      eq target1 target2 *> eq mot1 mot2 *> eq onLeft1 onLeft2 *> eq onRight1 onRight2
    (U, U) -> yes
    (l, r) -> no l r