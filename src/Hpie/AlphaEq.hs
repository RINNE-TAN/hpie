module Hpie.AlphaEq where

import Data.Foldable (traverse_)
import Hpie.Env (TcMonad)
import qualified Hpie.Env as Env
import Hpie.Types

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
  (<*>) f a = f >>= (<$> a)

instance Monad Alpha where
  (>>=) alphaA f =
    Alpha
      ( \l r i -> case runAlpha alphaA l r i of
          Left err -> Left err
          Right a -> runAlpha (f a) l r i
      )

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

alpha2tc :: Alpha a -> TcMonad a
alpha2tc alpha = case runAlpha alpha [] [] 0 of
  Left e -> Env.throwE e
  Right v -> return v

alphaEq :: Term -> Term -> TcMonad ()
alphaEq = \t1 t2 -> alpha2tc (go t1 t2)
  where
    go (Var x) (Var y) =
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
    go (Pi x1 a1 b1) (Pi x2 a2 b2) =
      go a1 a2 *> with x1 x2 (go b1 b2)
    go (Arrow a1 b1) (Arrow a2 b2) = go a1 a2 *> go b1 b2
    go (Lam x1 term1) (Lam x2 term2) =
      with x1 x2 (go term1 term2)
    go (Rec x1 term1) (Rec x2 term2) = with x1 x2 (go term1 term2)
    go (App f1 arg1) (App f2 arg2) = go f1 f2 *> go arg1 arg2
    go (Sigma x1 a1 b1) (Sigma x2 a2 b2) =
      go a1 a2 *> with x1 x2 (go b1 b2)
    go (Pair a1 b1) (Pair a2 b2) = go a1 a2 *> go b1 b2
    go (Prod l1 r1) (Prod l2 r2) =
      go l1 l2 *> go r1 r2
    go (First p1) (First p2) = go p1 p2
    go (Second p1) (Second p2) = go p1 p2
    go (TyCon x1 args1) (TyCon x2 args2) =
      rawEq x1 x2
        *> listEq args1 args2 go
    go (DataCon x1 args1) (DataCon x2 args2) =
      rawEq x1 x2
        *> listEq args1 args2 go
    go (Match term1 case1) (Match term2 case2) =
      go term1 term2
        *> listEq
          case1
          case2
          (\(Case pat1 c1) (Case pat2 c2) -> rawEq pat1 pat2 *> go c1 c2)
    go U U = yes
    go l r = no l r
