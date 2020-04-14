module Evaluator where

import           Types

eval :: Env -> Expr -> TypeCheck Value -- Evaluation
eval env (App e es) = do
  v <- eval env e
  vs <- mapM (eval env) es
  return $ VApp v vs
eval env Star = return VStar
eval env (Con name) = return $ VCon name
eval env (Def name) = return $ VDef name
eval env (Var name) = return $ lookupEnv env name
eval env (Lam x e) = return $ VLam x env e
eval env (Pi name ty e) = do
  ety <- eval env ty
  return $ VPi name ety env e
-- evaluation of size type
eval _env Size = return VSize -- size type
eval env (SuccS s) = do
  vs <- eval env s
  return $ sinfty vs -- size successor
eval _env Infty = return VInfty -- size infinity (limit size)

updateEnv :: Env -> Name -> Value -> Env
updateEnv env n v = (n, v) : env

lookupEnv :: Env -> Name -> Value
lookupEnv [] n = error $ "Empty environment. Cannot find " <> show n
lookupEnv ((x, v):xs) n =
  if x == n
    then v
    else lookupEnv xs n
