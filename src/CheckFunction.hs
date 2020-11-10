module CheckFunction where

import           CheckExpr           (checkExpr)
import           Control.Monad       (zipWithM_)
import           Control.Monad.State (get, put)
import           Evaluator           (eval)
import Pattern ( checkDot, checkPats )
import Coverage
import           Types
import Data.Maybe (fromMaybe)

-- check a list of functions
typeCheckFuns :: [(TypeSig, [Clause])] -> TypeCheck ()
typeCheckFuns funs = do
  mapM_ addFunSig funs -- add all funs in the list (non-typechecked) to the sig
  -- type check all clauses of all functions in the list
  zipWithM_ typeCheckFunClause [1 ..] funs
  mapM_ enableSig funs -- set typechecked field to True

-- add function n to the sig
addFunSig :: (TypeSig, [Clause]) -> TypeCheck ()
addFunSig (TypeSig n t, cl) = do
  sig <- get
  vt <- eval [] t
  -- typechecked field set to False because it's non-type/termination checked
  put (addSig sig n (FunSig vt cl False))

-- check all clauses of a function.
-- TODO add coverage check
typeCheckFunClause :: Int -> (TypeSig, [Clause]) -> TypeCheck ()
typeCheckFunClause _k (TypeSig _n t, cl) = checkFun t cl

checkFun :: Expr -> [Clause] -> TypeCheck ()
checkFun = checkFun' 1

checkFun' :: Int -> Expr -> [Clause] -> TypeCheck ()
checkFun' _i _e [] = return ()
checkFun' i e (c:cl) = do
  checkClause i e c
  checkFun' (i + 1) e cl

-- check each clause of a function separately:
-- first we check the patterns (see module Pattern)
-- and then the right hand side (e).
checkClause :: Int -> Expr -> Clause -> TypeCheck ()
checkClause _i e cl = do
  v <- eval [] e
  -- phase 1: check accessible patterns & inst dot patterns
  (k, flex, ins, rho, gamma, vt) <- 
    checkPats 0 [] [] [] [] v (namedClausePats cl)
  -- phase 2: check inaccessible patterns
  mapM_ (checkDot k rho gamma ins) flex
  -- check the right hand side (e)
  checkExpr k rho gamma (fromMaybe (undefined) (clauseBody cl)) vt

-- set the typechecked field in sig (of the function with name n) to True.
enableSig :: (TypeSig, [Clause]) -> TypeCheck ()
enableSig (TypeSig n _, _) = do
  sig <- get
  let (FunSig vt cl _) = lookupSig n sig
  put (addSig sig n (FunSig vt cl True))
