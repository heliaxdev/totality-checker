module Termination where

import           GHC.Generics (Generic)
import           TypeChecker

data Sized -- distinguish between sized and not sized data type.
  = Sized
  | NotSized
  deriving (Eq, Show)

data TypeSig =
  TypeSig Name ITerm
  deriving (Eq, Show)

data Declaration =
  DataDecl Name Sized Context ITerm [TypeSig]

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
