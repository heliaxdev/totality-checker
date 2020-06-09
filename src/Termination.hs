module Termination where

import           Data.Matrix
import           Data.Semiring
import qualified Data.Vector   as V
import           Types

-- arity of a clause. All clauses of a function should have the same arity.
arity :: Clause -> Int
arity (Clause pl _) = length pl

-- order = {<,≤,?} when comparing an expression e to a pattern p
data Order
  = Lt -- less than
  | Le -- less than or equal to
  | Un -- unknown
  | Mat (Matrix Order) -- square matrices only
  deriving (Show, Eq)

instance Semiring Order where
  zero = Un
  one = Le
  -- plus is also the order maximum function
  plus _ Lt  = Lt
  plus Lt _  = Lt
  plus Un x  = x
  plus x Un  = x
  plus Le Le = Le
  times Lt Un      = Un
  times Lt _       = Lt
  times Le o       = o
  times Un _       = Un
  times (Mat m) Le = Mat m
  times (Mat m) Un = Un
  times (Mat m) Lt = times (collapse m) Lt

-- returns the minimum of the input orders
orderMin :: Order -> Order -> Order
orderMin Un _ = Un
orderMin _ Un = Un
orderMin Lt o2 = o2
orderMin o1 Lt = o1
orderMin Le Le = Le
orderMin (Mat m1) (Mat m2) =
  if ncols m1 == ncols m2
    then Mat $ minM m1 m2
    else orderMin (collapse m1) (collapse m2)
orderMin (Mat m1) o2 = orderMin (collapse m1) o2
orderMin o1 (Mat m2) = orderMin o1 (collapse m2)

collapse :: Matrix Order -> Order
collapse m = minL (getDiag m)

-- returns the max order of a list
maxL :: V.Vector Order -> Order
maxL = V.foldl1 plus

-- returns the min order of a list
minL :: V.Vector Order -> Order
minL = V.foldl1 orderMin

minM :: Matrix Order -> Matrix Order -> Matrix Order
minM = undefined

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
    then undefined -- TODO Mat (V.map (\e -> (map (compareExpr e) pl)) (V.fromList args))
    else Un
compareExpr (Succ e2) (SuccP p2) = compareExpr e2 p2
compareExpr _ _ = Un

compareVar :: Name -> Pattern -> Order
compareVar n p =
  case p of
    VarP n2 ->
      if n == n2
        then Le
        else Un
    ConP c (p:pl) ->
      times Lt (maxL (V.map (compareVar n) (V.fromList (p : pl))))
    SuccP p2 -> times Lt (compareVar n p2)
    DotP e ->
      case (exprToPattern e) of
        Nothing -> Un
        Just p' -> compareVar n p'
    _ -> Un
