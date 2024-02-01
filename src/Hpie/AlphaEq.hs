module Hpie.AlphaEq where

import Hpie.Types

alphaEq :: Term -> Term -> Either () ()
alphaEq t1 t2 = runAlpha (eq t1 t2) [] [] 0

newtype Alpha a = Alpha
  { runAlpha ::
      [(Symbol, Int)] ->
      [(Symbol, Int)] ->
      Int ->
      Either () a
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

no :: Alpha ()
no = Alpha (\_ _ _ -> Left ())

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
              | otherwise -> Left ()
            (Just i, Just j)
              | i == j -> Right ()
              | otherwise -> Left ()
            _ -> Left ()
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
    (Nat, Nat) -> yes
    (Zero, Zero) -> yes
    (Succ n1, Succ n2) -> eq n1 n2
    (IndNat target1 mot1 base1 step1, IndNat target2 mot2 base2 step2) ->
      eq target1 target2 *> eq mot1 mot2 *> eq base1 base2 *> eq step1 step2
    (U, U) -> yes
    _ -> no