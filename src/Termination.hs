module Termination where

import           Data.Matrix
import           Data.Semiring
import qualified Data.Vector   as V
import           Types

-- order = {<,≤,?} when comparing an expression e to a pattern p
-- ? is the min, < is the max
data Order
  = Lt -- less than
  | Le -- less than or equal to
  | Un -- unknown
  | Mat (Matrix Order) -- square matrices only
  deriving (Show, Eq)

instance Semiring Order where
  zero = Un
  one = Le
  -- addition or parallel composition or the order maximum function
  plus _ Lt = Lt
  plus Lt _ = Lt
  plus Un x = x
  plus x Un = x
  plus Le Le = Le
  plus (Mat m1) (Mat m2) =
    if sameSizeMat m1 m2
      then Mat $ elementwise plus m1 m2
      else plus (collapse m1) (collapse m2)
  plus (Mat m) x = plus (collapse m) x
  plus x (Mat m) = plus x (collapse m)
  -- multiplication or serial composition
  times Lt Un = Un
  times Lt (Mat m) = times Lt (collapse m)
  times Lt _ = Lt
  times Le o = o
  times Un _ = Un
  times (Mat m1) (Mat m2) =
    if sameSizeMat m1 m2
      then Mat $ elementwise times m1 m2
      else times (collapse m1) (collapse m2)
  times (Mat m) Le = Mat m
  times (Mat m) Un = Un
  times (Mat m) Lt = times (collapse m) Lt

sameSizeMat :: Matrix Order -> Matrix Order -> Bool
sameSizeMat m1 m2 = ncols m1 == ncols m2 && nrows m1 == nrows m2

-- returns the minimum of the input orders
minOrder :: Order -> Order -> Order
minOrder Un _ = Un
minOrder _ Un = Un
minOrder Lt o2 = o2
minOrder o1 Lt = o1
minOrder Le Le = Le
minOrder (Mat m1) (Mat m2) =
  if sameSizeMat m1 m2
    then Mat $ elementwiseUnsafe minOrder m1 m2
    else minOrder (collapse m1) (collapse m2)
minOrder (Mat m1) o2 = minOrder (collapse m1) o2
minOrder o1 (Mat m2) = minOrder o1 (collapse m2)

collapse :: Matrix Order -> Order
collapse m = minL (V.toList (getDiag m))

-- returns the max order of a list
maxL :: [Order] -> Order
maxL = foldl1 plus

-- returns the min order of a list
minL :: [Order] -> Order
minL = foldl1 minOrder

exprToPattern :: Expr -> Maybe Pattern
exprToPattern (Var n) = Just $ VarP n
exprToPattern (Succ e) =
  case exprToPattern e of
    Nothing -> Nothing
    Just p  -> Just $ SuccP p
exprToPattern (App (Con n) el) =
  case exprsToPatterns el of
    Nothing -> Nothing
    Just pl -> Just $ ConP n pl
exprToPattern (Con n) = Just $ ConP n []
exprToPattern _ = Nothing

exprsToPatterns :: [Expr] -> Maybe [Pattern]
exprsToPatterns [] = Just []
exprsToPatterns (e:el) =
  case exprToPattern e of
    Nothing -> Nothing
    Just p ->
      case exprsToPatterns el of
        Nothing -> Nothing
        Just pl -> Just (p : pl)

compareExpr :: Expr -> Pattern -> Order
compareExpr e (DotP e') =
  case exprToPattern e' of
    Nothing ->
      if e == e'
        then Le
        else Un
    Just p' -> compareExpr e p'
compareExpr (Var i) p = compareVar i p
compareExpr (App (Var i) _) p = compareVar i p
compareExpr (Con n1) (ConP n2 []) =
  if n1 == n2
    then Le
    else Un
compareExpr (App (Con n1) [e1]) (ConP n2 [p1]) =
  if n1 == n2
    then compareExpr e1 p1
    else Un
compareExpr (App (Con n1) args) (ConP n2 pl) =
  if n1 == n2 && length args == length pl
    then minL $ concatMap (\e -> (map (compareExpr e) pl)) args
    else Un
compareExpr (Succ e2) (SuccP p2) = compareExpr e2 p2
compareExpr _ _ = Un

compareVar :: Name -> Pattern -> Order
compareVar n (VarP n2) =
  if n == n2
    then Le
    else Un
compareVar n (ConP c (p:pl)) = times Lt (maxL (map (compareVar n) (p : pl)))
compareVar n (SuccP p2) = times Lt (compareVar n p2)
compareVar n (DotP e) =
  case exprToPattern e of
    Nothing -> Un
    Just p' -> compareVar n p'
compareVar n _ = Un

data Call =
  Call
    { source :: Name -- Name of calling function f where f (p1 ...) = e
    , target :: Name -- Name of called function g, g (e1...) is a call in e
    , matrix :: Matrix Order -- the orders of e's and p's
    -- the rows represent the input parameters of the calling function
    -- and the columns the arguments of the called function.
    -- A “<” in cell (i, j) of a call matrix expresses that
    -- the j argument of the call is
    -- strictly smaller than the ith parameter of the calling function,
    -- a “≤” denotes weak decrease
    -- and a “?” stands for increase or absence of information
    }
  deriving (Eq, Show)

-- arity of a clause. All clauses of a function should have the same arity.
arity :: Clause -> Int
arity (Clause pl _) = length pl
