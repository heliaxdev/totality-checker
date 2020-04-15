-- Sized typed built on top of LambdaPi
module TypeChecker where

import           Control.Monad.State
import           Evaluator
import           Prelude
import           Types

checkExpr :: Int -> Env -> Env -> Expr -> Value -> TypeCheck ()
checkExpr k rho gamma (Lam n e1) (VPi x va env t1) = do
  v_t1 <- eval (updateEnv env x (VGen k)) t1
  checkExpr (k + 1) (updateEnv rho n (VGen k)) (updateEnv gamma n va) e1 v_t1
checkExpr k rho gamma (Pi n t1 t2) VStar = do
  checkExpr k rho gamma t1 VStar
  v_t1 <- eval rho t1
  checkExpr (k + 1) (updateEnv rho n (VGen k)) (updateEnv gamma n v_t1) t2 VStar
checkExpr k rho gamma (Succ e2) VSize = checkExpr k rho gamma e2 VSize
checkExpr k rho gamma e@_ _ = undefined

--   v2 <- inferExpr k rho gamma e
--   leqVal k v2 v
inferExpr :: Int -> Env -> Env -> Expr -> TypeCheck Value
inferExpr k rho gamma (Var x) = return $ lookupEnv gamma x
      --Size -> return VSet
inferExpr k rho gamma Infty = return VSize
inferExpr k rho gamma (App e1 [e2]) = do
  v <- inferExpr k rho gamma e1
  case v of
    VPi x av env b -> do
      checkExpr k rho gamma e2 av
      v2 <- eval rho e2
      eval (updateEnv env x v2) b
    _ ->
      error $
      "inferExpr : expected Pi with expression : " <> show e1 <> "," <> show v
inferExpr k rho gamma (App e1 (e2:el)) =
  inferExpr k rho gamma (App (App e1 [e2]) el)
inferExpr k rho gamma (Def n) = do
  sig <- get
  case lookupSig n sig of
    (DataSig _ _ _ tv) -> return tv
    (FunSig tv _ _)    -> return tv
inferExpr k rho gamma (Con n) = do
  sig <- get
  case lookupSig n sig of
    (ConSig tv) -> return tv
inferExpr k rho gamma e = error $ "cannot infer type " <> show e

checkT :: Expr -> TypeCheck ()
checkT = checkType 0 [] []

checkType :: Int -> Env -> Env -> Expr -> TypeCheck ()
checkType k rho gamma Star = return ()
checkType k rho gamma Size = return ()
checkType k rho gamma (Pi x t1 t2) = do
  checkType k rho gamma t1
  v_t1 <- eval rho t1
  checkType (k + 1) (updateEnv rho x (VGen k)) (updateEnv gamma x v_t1) t2
checkType k rho gamma e = checkExpr k rho gamma e VStar
