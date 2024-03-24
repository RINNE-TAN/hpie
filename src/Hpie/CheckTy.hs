module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import Hpie.Env (TcMonad, Ty)
import qualified Hpie.Env as Env
import qualified Hpie.Norm as Norm
import Hpie.Types

failCheck :: String -> Term -> TcMonad a
failCheck expected got = do
  gotNorm <- Norm.nbe got
  Env.throwE $ TypeMissMatch expected (show gotNorm)

infer :: Term -> TcMonad Ty
infer (Var x) = Env.searchTy x
infer (Pi x a b) = do
  check a U
  aNorm <- Norm.nbe a
  Env.extendEnv (IsA x aNorm) (check b U)
  return U
infer (Arrow a b) = do
  check a U
  check b U
  return U
infer (App f arg) = do
  fTy <- infer f
  case fTy of
    (Pi x aT bT) -> do
      check arg aT
      argNorm <- Norm.nbe arg
      Norm.doSubst (x, argNorm) bT
    _ -> failCheck "Pi Type" fTy
infer (Sigma x a b) = do
  check a U
  aNorm <- Norm.nbe a
  Env.extendEnv (IsA x aNorm) (check b U)
  return U
infer (Pair a b) = do
  check a U
  check b U
  return U
infer (First p) = do
  pTy <- infer p
  case pTy of
    (Sigma _ aT _) -> return aT
    _ -> failCheck "Sigma Type" pTy
infer (Second p) = do
  pTy <- infer p
  case pTy of
    (Sigma x _ bT) -> do
      firstNorm <- Norm.eval p >>= Norm.doFirst >>= Norm.reify
      Norm.doSubst (x, firstNorm) bT
    _ -> failCheck "Sigma Type" pTy
infer (TyCon symbol args) = do
  tyCon <- Env.searchTyCon symbol
  case tyCon of
    TyDef _ teles _ -> tcTeleArgs teles args
  return U
infer U = return U
infer other = Env.throwE $ CanNotInfer (show other)

check :: Term -> Ty -> TcMonad ()
check (Lam arg t) fTy = case fTy of
  (Pi x aT bT) -> do
    y <- Norm.fresh arg
    Env.extendEnv
      (IsA y aT)
      ( do
          tT <- Norm.doSubst (x, Var y) bT
          check t tT
      )
  _ -> failCheck "Pi Type" fTy
check (Prod first second) pTy = case pTy of
  (Sigma x aT bT) -> do
    check first aT
    firstNorm <- Norm.nbe first
    secondT <- Norm.doSubst (x, firstNorm) bT
    check second secondT
  _ -> failCheck "Sigma Type" pTy
check (DataCon dataSymbol dataArgs) ty = case ty of
  (TyCon tySymbol tyArgs) -> do
    (tyTeles, dataTeles) <- Env.searchTyConWithDataCon tySymbol dataSymbol
    extendTeleArgs
      tyTeles
      tyArgs
      ( tcTeleArgs dataTeles dataArgs
      )
    return ()
  _ -> failCheck "User Def Type" ty
check (Match term cases) ty = do
  termTy <- infer term
  mapM_ (tcCase termTy ty) cases
check _ TopTy = return ()
check other tTy = do
  tTy' <- infer other
  convert tTy tTy'

convert :: Term -> Term -> TcMonad ()
convert v1 v2 = do
  e1 <- Norm.nbe v1
  e2 <- Norm.nbe v2
  AlphaEq.alphaEq e1 e2

tcCase :: Ty -> Ty -> Case -> TcMonad ()
tcCase termTy ty (Case pat term) = extendPat pat termTy (check term ty)

extendPat :: Pattern -> Ty -> TcMonad a -> TcMonad a
extendPat (PatVar x) ty tc = Env.extendEnv (IsA x ty) tc
extendPat (PatCon dataSymbol pats) (TyCon tySymbol tyArgs) tc = do
  (tyTeles, dataTeles) <- Env.searchTyConWithDataCon tySymbol dataSymbol
  extendTeleArgs
    tyTeles
    tyArgs
    (extendPatTele pats dataTeles tc)

extendPatTele :: [Pattern] -> Tele -> TcMonad a -> TcMonad a
extendPatTele pats (tele@(Def _ _) : teles) tc = do
  extendTele [tele] (extendPatTele pats teles tc)
extendPatTele (pat : pats) (tele@(IsA _ ty) : teles) tc = do
  tyV <- Norm.nbe ty
  extendTele
    [tele]
    ( extendPat
        pat
        tyV
        ( extendPatTele pats teles tc
        )
    )
extendPatTele [] [] tc = tc
extendPatTele _ _ _ = Env.throwE ArgNumMissMatch

tcEntry :: Entry -> TcMonad Entry
tcEntry (IsA x a) = do
  check a U
  aNorm <- Norm.nbe a
  return (IsA x aNorm)
tcEntry (Def x a) = do
  xTy <- infer (Var x)
  check a xTy
  aNorm <- Norm.nbe a
  return (Def x aNorm)
tcEntry (TyDef symbol tele cs) = do
  tcTele tele
  let checkConDefWithDef conDef =
        Env.extendEnv
          (TyDef symbol tele [])
          $ extendTele tele (tcConDef conDef >> return conDef)
  ecs <- mapM checkConDefWithDef cs
  return (TyDef symbol tele ecs)

tcConDef :: DataDef -> TcMonad ()
tcConDef (DataDef _ tele) = tcTele tele

tcTele :: Tele -> TcMonad ()
tcTele [] = return ()
tcTele (x : xs) = do
  vEntry <- tcEntry x
  Env.extendEnv vEntry (tcTele xs)

extendTele :: Tele -> TcMonad a -> TcMonad a
extendTele xs tc = foldr go tc xs
  where
    go x after = do
      vEntry <- tcEntry x
      Env.extendEnv vEntry after

tcTeleArgs :: Tele -> [Term] -> TcMonad ()
tcTeleArgs ((Def x v) : teles) args = do
  xNorm <- Norm.nbe (Var x)
  vNorm <- Norm.nbe v
  AlphaEq.alphaEq xNorm vNorm
  tcTeleArgs teles args
tcTeleArgs (IsA x ty : teles) (arg : args) = do
  tyNorm <- Norm.nbe ty
  check arg tyNorm
  argNorm <- Norm.nbe arg
  Env.extendEnv (Def x argNorm) (tcTeleArgs teles args)
tcTeleArgs (IsA _ _ : _) [] = Env.throwE ArgNumMissMatch
tcTeleArgs [] (_ : _) = Env.throwE ArgNumMissMatch
tcTeleArgs [] [] = return ()

extendTeleArgs :: Tele -> [Term] -> TcMonad a -> TcMonad a
extendTeleArgs (entry@(Def _ _) : teles) args tc = do
  entryV <- tcEntry entry
  Env.extendEnv entryV (extendTeleArgs teles args tc)
extendTeleArgs (entry@(IsA x _) : teles) (arg : args) tc = do
  entryV <- tcEntry entry
  argNorm <- Norm.nbe arg
  Env.extendEnv
    entryV
    ( Env.extendEnv (Def x argNorm) (extendTeleArgs teles args tc)
    )
extendTeleArgs [] [] tc = tc