module Evaluator where

import           Control.Monad.State
import           Types

eval :: Env -> Expr -> TypeCheck Value -- Evaluation
eval env (App e es) = do
  v <- eval env e
  vs <- mapM (eval env) es
  return $ VApp v vs
eval _env Star = return VStar
eval _env (Con name) = return $ VCon name
eval _env (Def name) = return $ VDef name
eval env (Var name) = return $ lookupEnv env name
eval env (Lam x e) = return $ VLam x env e
eval env (Pi name ty e) = do
  ety <- eval env ty
  return $ VPi name ety env e
-- evaluation of size type
eval _env Size = return VSize
eval env (Succ s) = do
  vs <- eval env s
  return $ sinfty vs
eval _env Infty = return VInfty

updateEnv :: Env -> Name -> Value -> Env
updateEnv env n v = (n, v) : env

lookupEnv :: Env -> Name -> Value
lookupEnv [] n = error $ "Empty environment. Cannot find " <> show n
lookupEnv ((x, v):xs) n
  | x == n = v
  | otherwise = lookupEnv xs n

app :: Value -> [Value] -> TypeCheck Value
app u [] = return u
app (VApp u2 c2) c = app u2 (c2 <> c)
app (VLam x env e) (v:vl) = do
  v' <- eval (updateEnv env x v) e
  app v' vl
app (VDef n) c = appDef n c
app u c = return $ VApp u c

appDef :: Name -> [Value] -> TypeCheck Value
appDef n vl = do
  sig <- get
  case lookupSig n sig of
    (FunSig _ cl True) -> do
      m <- matchClauses cl vl
      case m of
        Nothing -> return $ VApp (VDef n) vl
        Just v2 -> return v2
    _ -> return $ VApp (VDef n) vl

-- pattern matching
matchClauses :: [Clause] -> [Value] -> TypeCheck (Maybe Value)
matchClauses cl cll = loop cl
  where
    loop [] = return Nothing
    loop (Clause pl rhs:cl2) = do
      x <- matchClause [] pl rhs cll
      case x of
        Nothing -> loop cl2
        Just v  -> return $ Just v

matchClause :: Env -> [Pattern] -> Expr -> [Value] -> TypeCheck (Maybe Value)
matchClause env [] rhs vl = do
  v <- eval env rhs
  v2 <- app v vl
  return $ Just v2
matchClause env (p:pl) rhs (v:vl) = do
  m <- match env p v
  case m of
    Just env' -> matchClause env' pl rhs vl
    Nothing   -> return Nothing
matchClause _ _ _ [] = return Nothing

match :: Env -> Pattern -> Value -> TypeCheck (Maybe Env)
match env (DotP _) _ = return $ Just env
match env (VarP x) v = return $ Just (updateEnv env x v)
match env (ConP name []) (VCon y)
  | name == y = return $ Just env
match env (ConP name pl) (VApp (VCon y) vl)
  | name == y = matchList env pl vl
match env (SuccP p') VInfty = match env p' VInfty
match env (SuccP p') (VSucc v') = match env p' v'
match _env _p _v = return Nothing

matchList :: Env -> [Pattern] -> [Value] -> TypeCheck (Maybe Env)
matchList env [] [] = return $ Just env
matchList env (p:pl) (v:vl) = do
  m <- match env p v
  case m of
    Just env' -> matchList env' pl vl
    Nothing   -> return Nothing
matchList _ _ _ = return Nothing

-- check that a does not occur in tv
-- a may be a "atomic value" i.e not pi , lam , app , or succ
nocc :: Int -> Value -> Value -> TypeCheck Bool
nocc k a tv =
  case tv of
    VPi x av env b -> do
      no <- nocc k a av
      if no
        then do
          bv <- eval (updateEnv env x (VGen k)) b
          nocc (k + 1) a bv
        else return False
    VLam x env b -> do
      bv <- eval (updateEnv env x (VGen k)) b
      nocc (k + 1) a bv
    VSucc v -> nocc k a v
    VApp v1 vl -> do
      n <- nocc k a v1
      nl <- mapM (nocc k a) vl
      return $ n && and nl
    _ -> return $ a /= tv
