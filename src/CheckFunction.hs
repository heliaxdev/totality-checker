module CheckFunction where

import           CheckExpr           (checkExpr, checkType0)
import           Control.Monad       (unless, zipWithM_)
import           Control.Monad.State (get, put)
import           Evaluator           (eval)
import           Pattern
import           Types

typeCheckFuns :: [(TypeSig, [Clause])] -> TypeCheck ()
typeCheckFuns funs = do
  mapM_ addFunSig funs
  zipWithM_ typeCheckFunClause [1 ..] funs
  mapM_ enableSig funs

addFunSig :: (TypeSig, [Clause]) -> TypeCheck ()
addFunSig (TypeSig n t, cl) = do
  sig <- get
  vt <- eval [] t
  put (addSig sig n (FunSig vt cl False)) --not yet type checked / termination checked

typeCheckFunClause :: Int -> (TypeSig, [Clause]) -> TypeCheck ()
typeCheckFunClause _k (TypeSig _n t, cl) = checkFun t cl

-- We need to check all clauses of a function.
checkFun :: Expr -> [Clause] -> TypeCheck ()
checkFun = checkFun' 1

checkFun' :: Int -> Expr -> [Clause] -> TypeCheck ()
checkFun' i e [] = return ()
checkFun' i e (c:cl) = do
  checkClause i e c
  checkFun' (i + 1) e cl

-- We need to check each clause of a function separately:
-- first we check the patterns (see module Pattern)
-- and then the right hand side (e).
checkClause :: Int -> Expr -> Clause -> TypeCheck ()
checkClause i e (Clause pl rhs) = do
  v <- eval [] e
  -- check accessible patterns
  (k, flex, ins, rho, gamma, vt) <- checkPatterns 0 [] [] [] [] v pl
  -- check inaccessible patterns
  mapM_ (checkDot k rho gamma ins) flex
  -- check the right hand side (e)
  checkExpr k rho gamma rhs vt

enableSig :: (TypeSig, [Clause]) -> TypeCheck ()
enableSig (TypeSig n _, _) = do
  sig <- get
  let (FunSig vt cl _) = lookupSig n sig
  put (addSig sig n (FunSig vt cl True))
