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
      Norm.doSubst (x, argNorm) bT >>= Norm.nbe
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
      firstNorm <- Norm.nbe (First p)
      Norm.doSubst (x, firstNorm) bT >>= Norm.nbe
    _ -> failCheck "Sigma Type" pTy
infer (TyCon symbol args) = do
  tyCon <- Env.searchTyCon symbol
  case tyCon of
    TyDef _ teles _ -> tcTeleArgs teles args >> return U
infer U = return U
infer other = Env.throwE $ CanNotInfer (show other)

check :: Term -> Ty -> TcMonad ()
check (Lam arg body) fTy = case fTy of
  (Pi x aT bT) -> do
    newArg <- Norm.fresh arg
    aTNorm <- Norm.nbe aT
    Env.extendTele
      [IsA newArg aTNorm]
      ( do
          bTNorm <- Norm.doSubst (x, Var newArg) bT >>= Norm.nbe
          newBody <- Norm.doSubst (arg, Var newArg) body
          check newBody bTNorm
      )
  _ -> failCheck "Pi Type" fTy
check (Prod first second) pTy = case pTy of
  (Sigma x aT bT) -> do
    check first aT
    firstNorm <- Norm.nbe first
    secondT <- Norm.doSubst (x, firstNorm) bT >>= Norm.nbe
    check second secondT
  _ -> failCheck "Sigma Type" pTy
check (DataCon dataSymbol dataArgs) ty = case ty of
  (TyCon tySymbol tyArgs) -> do
    (tyTeles, dataTeles) <- Env.searchTyConWithDataCon tySymbol dataSymbol
    newTyTeles <- tcTeleArgs tyTeles tyArgs
    _ <-
      Env.extendTele
        newTyTeles
        (tcTeleArgs dataTeles dataArgs)
    return ()
  _ -> failCheck "User Def Type" ty
check (Match m cases) ty = do
  mTy <- infer m
  mNorm <- Norm.nbe m
  mapM_ (tcCase mNorm mTy ty) cases
check TODO ty = do
  Env.logInfo ("Found TODO, expected: ", ty)
  return ()
check other tTy = do
  tTy' <- infer other
  convert tTy tTy'

convert :: Term -> Term -> TcMonad ()
convert v1 v2 = do
  e1 <- Norm.nbe v1
  e2 <- Norm.nbe v2
  AlphaEq.alphaEq e1 e2

tcCase :: Term -> Ty -> Ty -> Case -> TcMonad ()
tcCase mNorm mTy ty (Case pat body) = do
  (newPat, newBody) <- freshPatBody pat body
  patTeles <- tcPat newPat mTy
  patTerm <- pat2Term newPat
  mTeles <- AlphaEq.unify mNorm patTerm
  Env.extendTele (patTeles ++ mTeles) (check newBody ty)

freshPatBody :: Pattern -> Term -> TcMonad (Pattern, Term)
freshPatBody (PatVar x) body = do
  newX <- Norm.fresh x
  newBody <- Norm.doSubst (x, Var newX) body
  return (PatVar newX, newBody)
freshPatBody (PatCon dataSymbol pats) body = do
  (newPats, newBody) <- freshPatsBody pats body
  return (PatCon dataSymbol newPats, newBody)

freshPatsBody :: [Pattern] -> Term -> TcMonad ([Pattern], Term)
freshPatsBody [] body = return ([], body)
freshPatsBody (pat : pats) body = do
  (newPat, newBody) <- freshPatBody pat body
  (newPats, resBody) <- inBoundPat [newPat] (freshPatsBody pats newBody)
  return (newPat : newPats, resBody)

inBoundPat :: [Pattern] -> TcMonad a -> TcMonad a
inBoundPat ((PatVar x) : xs) tc = Env.inBound x (inBoundPat xs tc)
inBoundPat ((PatCon _ pats) : xs) tc = inBoundPat (pats ++ xs) tc
inBoundPat [] tc = tc

pat2Term :: Pattern -> TcMonad Term
pat2Term (PatVar x) = return (Var x)
pat2Term (PatCon dataSymbol pats) = DataCon dataSymbol <$> mapM pat2Term pats

tcPat :: Pattern -> Ty -> TcMonad Tele
tcPat (PatVar x) ty = return [IsA x ty]
tcPat (PatCon dataSymbol pats) (TyCon tySymbol tyArgs) = do
  (tyTeles, dataTeles) <- Env.searchTyConWithDataCon tySymbol dataSymbol
  newTyTeles <- tcTeleArgs tyTeles tyArgs
  Env.extendTele
    newTyTeles
    (tcPatTele pats dataTeles)

tcPatTele :: [Pattern] -> Tele -> TcMonad Tele
tcPatTele pats (Def x term : teles) = do
  xNorm <- Norm.nbe (Var x)
  termNorm <- Norm.nbe term
  unifyTeles <- AlphaEq.unify xNorm termNorm
  let tele = unifyTeles
  telesV <- Env.extendTele tele (tcPatTele pats teles)
  return (tele ++ telesV)
tcPatTele (pat : pats) (tele@(IsA _ ty) : teles) = do
  tyV <- Norm.nbe ty
  patTelesV <- tcPat pat tyV
  telesV <- Env.extendTele (tele : patTelesV) (tcPatTele pats teles)
  return (patTelesV ++ telesV)
tcPatTele [] [] = return []
tcPatTele _ _ = Env.throwE ArgNumMissMatch

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
  teleV <- tcTele tele
  let checkConDefWithDef conDef@(DataDef _ dataTele) =
        Env.extendEnv
          (TyDef symbol teleV [])
          $ Env.extendTele teleV (tcTele dataTele >> return conDef)
  ecs <- mapM checkConDefWithDef cs
  return (TyDef symbol teleV ecs)

tcTele :: Tele -> TcMonad Tele
tcTele [] = return []
tcTele (x : xs) = do
  xV <- tcEntry x
  xsV <- Env.extendEnv xV (tcTele xs)
  return (xV : xsV)

tcTeleArgs :: Tele -> [Term] -> TcMonad Tele
tcTeleArgs ((Def x v) : teles) args = do
  xNorm <- Norm.nbe (Var x)
  vNorm <- Norm.nbe v
  AlphaEq.alphaEq xNorm vNorm
  let teleV = Def x vNorm
  telesV <- Env.extendEnv teleV (tcTeleArgs teles args)
  return (teleV : telesV)
tcTeleArgs (IsA x ty : teles) (arg : args) = do
  tyNorm <- Norm.nbe ty
  check arg tyNorm
  argNorm <- Norm.nbe arg
  let teleV = [IsA x tyNorm, Def x argNorm]
  telesV <- Env.extendTele teleV (tcTeleArgs teles args)
  return (teleV ++ telesV)
tcTeleArgs (_ : _) [] = Env.throwE ArgNumMissMatch
tcTeleArgs [] (_ : _) = Env.throwE ArgNumMissMatch
tcTeleArgs [] [] = return []
