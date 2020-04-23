module CheckDataDecl where

import           CheckExpr
import           Control.Monad.State
import           Evaluator
import           SPos
import           Types

typeCheckConstructor ::
     Name -> Sized -> [Pos] -> Telescope -> TypeSig -> TypeCheck ()
typeCheckConstructor name sz pos tel (TypeSig n t) = do
  sig <- get
  let tt = teleToType tel t
      params = length tel
      p' =
        case sz of
          Sized    -> params + 1
          NotSized -> params
  checkConType 0 [] [] p' tt
  let (_, target) = typeToTele tt
  checkTarget name tel target
  vt <- eval [] tt
  sposConstructor name 0 pos vt
  put (addSig sig n (ConSig vt))

teleToType :: Telescope -> Expr -> Expr
teleToType [] t            = t
teleToType ((n, t):tel) t2 = Pi n t (teleToType tel t2)

typeToTele :: Expr -> (Telescope, Expr)
typeToTele t = ttt t []
  where
    ttt :: Expr -> Telescope -> (Telescope, Expr)
    ttt (Pi n t' t2) tel = ttt t2 (tel <> [(n, t')])
    ttt x tel            = (tel, x)

-- checks that input Expr denotes a valid type
checkT :: Expr -> TypeCheck ()
checkT = checkType 0 [] []

checkType :: Int -> Env -> Env -> Expr -> TypeCheck ()
checkType _k _rho _gamma Star = return ()
checkType _k _rho _gamma Size = return ()
checkType k rho gamma (Pi x t1 t2) = do
  checkType k rho gamma t1
  v_t1 <- eval rho t1
  checkType (k + 1) (updateEnv rho x (VGen k)) (updateEnv gamma x v_t1) t2
checkType k rho gamma e = checkExpr k rho gamma e VStar

-- check that input Expr is a star type
checkSType :: Int -> Env -> Env -> Expr -> TypeCheck ()
checkSType k rho gamma e = checkExpr k rho gamma e VStar

-- check that params are types
-- check that arguments are stypes
-- check that target is set
checkDataType :: Int -> Env -> Env -> Int -> Expr -> TypeCheck ()
checkDataType k rho gamma p (Pi x t1 t2) = do
  if k < p
    then checkType k rho gamma t1
    else checkSType k rho gamma t1
  v_t1 <- eval rho t1
  checkDataType (k + 1) (updateEnv rho x (VGen k)) (updateEnv gamma x v_t1) p t2
checkDataType _k _rho _gamma _p Star = return ()
checkDataType _k _rho _gamma _p e = error $ show e <> "doesn't target Star"

-- check that arguments are stypes
-- check that result is a set
--  ( params were already checked by checkDataType )
checkConType :: Int -> Env -> Env -> Int -> Expr -> TypeCheck ()
checkConType k rho gamma p e = undefined

-- check that the data type and the parameter arguments (written down like declared in telescope)
checkTarget :: Name -> Telescope -> Expr -> TypeCheck ()
checkTarget d tel tg = undefined
