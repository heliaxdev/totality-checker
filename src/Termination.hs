module Termination where

import           GHC.Generics (Generic)

data Totality
  = Total [Int] -- well-founded arguments
  | Partial
  | Unchecked
  -- | Productive -- not checking productivity atm
  deriving (Eq, Generic)

instance Show Totality where
  show (Total args) =
    "Total, with argument(s) " <> show args <> " which terminate(s)."
  show Unchecked = "not yet checked for totality"
  show Partial = "not total"
