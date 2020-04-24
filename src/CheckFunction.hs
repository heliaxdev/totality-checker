module CheckFunction where

import           CheckExpr           (checkType0)
import           Control.Monad       (unless, zipWithM_)
import           Control.Monad.State (get, put)
import           Evaluator           (eval)
import           Types

typeCheckFuns :: [(TypeSig, [Clause])] -> TypeCheck ()
typeCheckFuns funs = do
  mapM_ addFunSig funs
  mapM_ typeCheckFunSig funs
  zipWithM_ typeCheckFunClause [1 ..] funs
  mapM_ enableSig funs

addFunSig :: (TypeSig, [Clause]) -> TypeCheck ()
addFunSig (TypeSig n t, cl) = do
  sig <- get
  vt <- eval [] t
  put (addSig sig n (FunSig vt cl False)) --not yet type checked / termination checked

typeCheckFunSig :: (TypeSig, [Clause]) -> TypeCheck ()
typeCheckFunSig (TypeSig n t, cl) = do
  checkType0 t
  unless (completeFun cl) (error $ n <> " : size pattern incomplete")

typeCheckFunClause :: Int -> (TypeSig, [Clause]) -> TypeCheck ()
typeCheckFunClause _k (TypeSig _n t, cl) = checkFun t cl

enableSig :: (TypeSig, [Clause]) -> TypeCheck ()
enableSig (TypeSig n _, _) = do
  sig <- get
  let (FunSig vt cl _) = lookupSig n sig
  put (addSig sig n (FunSig vt cl True))

completeFun :: [Clause] -> Bool
completeFun cl = undefined

checkFun :: Expr -> [Clause] -> TypeCheck ()
checkFun e cl = undefined
