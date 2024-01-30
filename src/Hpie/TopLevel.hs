module Hpie.TopLevel where

import qualified Hpie.AlphaEq as AlphaEq
import qualified Hpie.CheckTy as CheckTy
import qualified Hpie.Norm as Norm
import Hpie.Parser
import Hpie.Types

newtype TopCtxWorker a = TopCtxWorker
  { runTopCtxWorker :: Env (CtxEntry Value) -> Either () (Env (CtxEntry Value), a)
  }

instance Functor TopCtxWorker where
  fmap f (TopCtxWorker wa) = TopCtxWorker (fmap (fmap f) . wa)

instance Applicative TopCtxWorker where
  pure x = TopCtxWorker (\e -> Right (e, x))
  (<*>) (TopCtxWorker wab) (TopCtxWorker wa) =
    TopCtxWorker
      ( \e -> do
          (e2, ab) <- wab e
          (e3, a) <- wa e2
          return (e3, ab a)
      )

instance Monad TopCtxWorker where
  (>>=) (TopCtxWorker wa) f =
    TopCtxWorker
      ( \e -> do
          (e2, a) <- wa e
          runTopCtxWorker (f a) e2
      )

topLevelMain :: String -> [TopLevelMsg]
topLevelMain s = case runTopCtxWorker (topLevel s) (Env []) of
  Left () -> error ""
  Right (_, v) -> v

parser :: String -> Parser a -> TopCtxWorker a
parser input pa =
  TopCtxWorker
    ( \e -> case runParser pa input of
        Left msg -> error $ show msg
        Right (_, v) -> Right (e, v)
    )

addDef :: Symbol -> CtxEntry Value -> TopCtxWorker ()
addDef s e =
  TopCtxWorker
    ( \ctx -> Right (extend ctx (s, e), ())
    )

ctxWorker :: CtxWorker a -> TopCtxWorker a
ctxWorker ctx =
  TopCtxWorker
    ( \e -> (\x -> (e, x)) <$> runCtxWorker ctx e
    )

worker :: Worker a -> TopCtxWorker a
worker = ctxWorker . toCtxWorker

eval :: Term -> TopCtxWorker Value
eval = worker . Norm.eval

reify :: Value -> TopCtxWorker Term
reify = worker . Norm.reify

check :: Term -> Value -> TopCtxWorker ()
check term ty = ctxWorker $ CheckTy.check term ty

lookupTy :: Symbol -> TopCtxWorker Value
lookupTy = ctxWorker . CheckTy.lookupTy

runOne :: TopLevel -> TopCtxWorker TopLevelMsg
runOne (Claim x t) = do
  ty <- eval t
  tNorm <- reify ty
  _ <- addDef x (IsA ty)
  return $ AddClaim x tNorm
runOne (Define x e) = do
  ty <- lookupTy x
  tyNorm <- reify ty
  _ <- check e ty
  eV <- eval e
  eNorm <- reify eV
  _ <- addDef x (Def eV ty)
  return $ AddDefine x eNorm tyNorm
runOne (CheckSame ty e1 e2) = do
  tyV <- eval ty
  e1V <- eval e1
  e2V <- eval e2
  e1Norm <- reify e1V
  e2Norm <- reify e2V
  _ <- check e1Norm tyV
  _ <- check e2Norm tyV
  case AlphaEq.alphaEq e1Norm e2Norm of
    Left () -> return NotSame
    Right () -> return IsSame

topLevel :: String -> TopCtxWorker [TopLevelMsg]
topLevel input = do
  tops <- parser input pProg
  foldr
    ( \curWork tailWork -> do
        cur <- runOne curWork
        tails <- tailWork
        return $ cur : tails
    )
    (return [])
    tops
