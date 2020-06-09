module Termination where

import           Data.Semiring
import           Types

-- order = {<,≤,?} when comparing an expression e to a pattern p
data Order
  = Lt -- less than
  | Le -- less than or equal to
  | Un -- unknown
  -- | Mat (Matrix Order) -- square matrices only
  deriving (Show, Eq, Ord)

instance Semiring Order where
  zero = Un
  one = Le
  plus _ Lt  = Lt
  plus Lt _  = Lt
  plus Un x  = x
  plus x Un  = x
  plus Le Le = Le
  times Lt Un = Un
  times Lt _  = Lt
  times Le o  = o
  times Un _  = Un

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
