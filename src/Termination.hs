module Termination where

-- order = {<,≤,?} when comparing an expression e to a pattern p
data Order
  = Lt -- less than
  | Le -- less than or equal to
  | Un -- unknown
  -- | Mat (Matrix Order) -- square matrices only
  deriving (Show, Eq, Ord)
