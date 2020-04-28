module CheckDataType where

import           CheckExpr
import           Control.Monad.State
import           Evaluator
import           SPos
import           Types

typeCheckConstructor ::
     Name -> Sized -> [Pos] -> Telescope -> TypeSig -> TypeCheck ()
typeCheckConstructor name sz pos tel (TypeSig n t) = do
  sig <- get -- get signatures
  let tt = teleToType tel t
      params = length tel
      p' =
        case sz of
          Sized    -> params + 1
          NotSized -> params
  _ <- checkConType 0 [] [] p' tt
  let (_, target) = typeToTele tt
  checkTarget name tel target
  vt <- eval [] tt
  sposConstructor name 0 pos vt -- strict positivity check
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

-- check data type
-- check that params are types
-- check that arguments are stypes
-- check that target is set
checkDataType :: Int -> Env -> Env -> Int -> Expr -> TypeCheck ()
checkDataType k rho gamma p (Pi x t1 t2) = do
  _ <-
    if k < p
      then checkType k rho gamma t1
      else checkSType k rho gamma t1
  v_t1 <- eval rho t1
  checkDataType (k + 1) (updateEnv rho x (VGen k)) (updateEnv gamma x v_t1) p t2
checkDataType _k _rho _gamma _p Star = return ()
checkDataType _k _rho _gamma _p e =
  error $ "checkDataType: " <> show e <> "doesn't target Star."

-- check constructor type
-- check that arguments are stypes
-- check that result is a star
--  ( params were already checked by checkDataType )
checkConType :: Int -> Env -> Env -> Int -> Expr -> TypeCheck (Either String ())
checkConType k rho gamma p (Pi x t1 t2) = do
  _ <-
    if k < p
      then return $ Right ()
      else checkSType k rho gamma t1
  v_t1 <- eval rho t1
  checkConType (k + 1) (updateEnv rho x (VGen k)) (updateEnv gamma x v_t1) p t2
checkConType k rho gamma _p e = checkExpr k rho gamma e VStar

-- check that the data type and the parameter arguments
-- are written down like declared in telescope
checkTarget :: Name -> Telescope -> Expr -> TypeCheck ()
checkTarget name tel tg@(App (Def n) al) =
  if n == name
    then do
      let pn = length tel
          params = take pn al
      checkPs tel params -- check parameters
    else error $
         "checkTarget: target mismatch " <> show tg <> ". Input name is " <>
         show name <>
         ". Input telescope is " <>
         show tel
checkTarget name tel tg@(Def n) =
  if n == name && null tel
    then return ()
    else error $
         "checkTarget: target mismatch" <> show tg <> ". Input name is " <>
         show name <>
         ". Input telescope is " <>
         show tel
checkTarget name tel tg =
  error $
  "checkTarget: target mismatch" <> show tg <> ". Input name is " <> show name <>
  ". Input telescope is " <>
  show tel

-- check parameters
checkPs :: Telescope -> [Expr] -> TypeCheck ()
checkPs [] [] = return ()
checkPs tel@((n, _t):tl) (Var n':el) =
  if n == n'
    then checkPs tl el
    else error $
         "checkPs: target parameter mismatch. The input telescope is " <>
         show tel <>
         ". One of the name in the telescope is " <>
         show n <> -- using show to wrap n with "
         ", which does not match the input expression's variable name: " <>
         show n'
checkPs _ _ =
  error
    "checkPs: target parameter mismatch. The input expression isn't a variable (Var)."
