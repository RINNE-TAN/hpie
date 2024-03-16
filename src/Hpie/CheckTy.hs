module Hpie.CheckTy where

import qualified Hpie.AlphaEq as AlphaEq
import Hpie.Env (Neutral (..), TcMonad, Ty, VEntry (..), Value (..))
import qualified Hpie.Env as Env
import qualified Hpie.Norm as Norm
import Hpie.Types

failCheck :: String -> Value -> TcMonad a
failCheck expected got = do
  gotNorm <- Norm.reify got
  Env.throwE $ TypeMissMatch expected (show gotNorm)

infer :: Term -> TcMonad Ty
infer (Var x) = Env.searchTy x
infer (Pi x a b) = do
  check a VU
  aV <- Norm.eval a
  Env.extendEnv (VIsA x aV) (check b VU)
  return VU
infer (Arrow a b) = do
  check a VU
  check b VU
  return VU
infer (App f arg) = do
  fTy <- infer f
  case fTy of
    (VPi aT closure) -> do
      check arg aT
      argV <- Norm.eval arg
      Norm.doApplyClosure closure argV
    _ -> failCheck "Pi Type" fTy
infer (Sigma x a b) = do
  check a VU
  va <- Norm.eval a
  Env.extendEnv (VIsA x va) (check b VU)
  return VU
infer (Pair a b) = do
  check a VU
  check b VU
  return VU
infer (First p) = do
  pTy <- infer p
  case pTy of
    (VSigma aT _) -> return aT
    _ -> failCheck "Sigma Type" pTy
infer (Second p) = do
  pTy <- infer p
  pV <- Norm.eval p
  case pTy of
    (VSigma _ closure) -> do
      firstV <- Norm.doFirst pV
      Norm.doApplyClosure closure firstV
    _ -> failCheck "Sigma Type" pTy
infer (TyCon symbol args) = do
  tyCon <- Env.searchTyCon symbol
  case tyCon of
    VTyDef _ teles _ -> tcTeleArgs teles args
  return VU
infer U = return VU
infer other = Env.throwE $ CanNotInfer (show other)

check :: Term -> Ty -> TcMonad ()
check (Lam x t) fTy = case fTy of
  (VPi aT closure) -> do
    y <- Norm.fresh x
    tT <- Norm.doApplyClosure closure (VNeutral (NVar y))
    Env.extendEnv (VIsA y aT) (check t tT)
  _ -> failCheck "Pi Type" fTy
check v@(Rec recf t) ty = do
  vV <- Norm.eval v
  Env.extendEnv (VDef recf vV) (check t ty)
check (Prod first second) pTy = case pTy of
  (VSigma aT closure) -> do
    check first aT
    firstV <- Norm.eval first
    secondT <- Norm.doApplyClosure closure firstV
    check second secondT
  _ -> failCheck "Sigma Type" pTy
check (DataCon dataSymbol dataArgs) ty = case ty of
  (VTyCon tySymbol tyArgs) -> do
    (tyTeles, dataTeles) <- Env.searchTyConWithDataCon tySymbol dataSymbol
    extendTeleArgs
      tyTeles
      tyArgs
      ( tcTeleArgs dataTeles dataArgs
      )
    return ()
  _ -> failCheck "User Def Type" ty
check (Match term cases) ty = do
  headTy <- infer term
  mapM_ (tcCase headTy ty) cases
check other tTy = do
  tTy' <- infer other
  convert tTy tTy'

convert :: Value -> Value -> TcMonad ()
convert v1 v2 = do
  e1 <- Norm.reify v1
  e2 <- Norm.reify v2
  AlphaEq.alphaEq e1 e2

tcCase :: Ty -> Ty -> Case -> TcMonad ()
tcCase headTy ty (Case pat term) = extendPat pat headTy (check term ty)

extendPat :: Pattern -> Ty -> TcMonad a -> TcMonad a
extendPat (PatVar x) ty tc = Env.extendEnv (VIsA x ty) tc
extendPat (PatCon dataSymbol pats) (VTyCon tySymbol tyArgs) tc = do
  (tyTeles, dataTeles) <- Env.searchTyConWithDataCon tySymbol dataSymbol
  extendTeleArgs
    tyTeles
    tyArgs
    (extendPatTele pats dataTeles tc)

extendPatTele :: [Pattern] -> Tele -> TcMonad a -> TcMonad a
extendPatTele pats (tele@(Def _ _) : teles) tc = do
  extendTele [tele] (extendPatTele pats teles tc)
extendPatTele (pat : pats) (tele@(IsA _ ty) : teles) tc = do
  tyV <- Norm.eval ty
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

tcEntry :: Entry -> TcMonad VEntry
tcEntry (IsA x a) = do
  check a VU
  aV <- Norm.eval a
  return (VIsA x aV)
tcEntry (Def x a) = do
  xTy <- infer (Var x)
  check a xTy
  aV <- Norm.eval a
  return (VDef x aV)
tcEntry (TyDef symbol tele cs) = do
  tcTele tele
  let checkConDefWithDef conDef =
        Env.extendEnv
          (VTyDef symbol tele [])
          $ extendTele tele (tcConDef conDef)
  ecs <- mapM checkConDefWithDef cs
  return (VTyDef symbol tele ecs)

tcConDef :: DataDef -> TcMonad (Symbol, Tele)
tcConDef (DataDef symbol tele) = do
  tcTele tele
  return (symbol, tele)

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
  xV <- Norm.eval (Var x)
  xNorm <- Norm.reify xV
  vV <- Norm.eval v
  vNorm <- Norm.reify vV
  AlphaEq.alphaEq xNorm vNorm
  tcTeleArgs teles args
tcTeleArgs (IsA x ty : teles) (arg : args) = do
  tyV <- Norm.eval ty
  check arg tyV
  argV <- Norm.eval arg
  Env.extendEnv (VDef x argV) (tcTeleArgs teles args)
tcTeleArgs (IsA _ _ : _) [] = Env.throwE ArgNumMissMatch
tcTeleArgs [] (_ : _) = Env.throwE ArgNumMissMatch
tcTeleArgs [] [] = return ()

extendTeleArgs :: Tele -> [Value] -> TcMonad a -> TcMonad a
extendTeleArgs (entry@(Def _ _) : teles) args tc = do
  entryV <- tcEntry entry
  Env.extendEnv entryV (extendTeleArgs teles args tc)
extendTeleArgs (IsA x _ : teles) (arg : args) tc = Env.extendEnv (VDef x arg) (extendTeleArgs teles args tc)
extendTeleArgs [] [] tc = tc