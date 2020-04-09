module Termination where

import           GHC.Generics (Generic)
import           SPos
import           Types

data Sized -- distinguish between sized and not sized data type.
  = Sized
  | NotSized
  deriving (Eq, Show)

data TypeSig =
  TypeSig Name ITerm
  deriving (Eq, Show)

type TBind = (Name, ITerm)

-- A telescope (context) is a sequence of types
-- where later types may depend on elements of previous types.
type Telescope = [TBind]

data Declaration =
  DataDecl Name Sized [Pos] Telescope ITerm [TypeSig]

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

-- equivalent to teleToType function in paper. Used in typeCheckDeclaration.
teleToITerm :: Telescope -> ITerm -> ITerm
teleToITerm [] t             = t
teleToITerm ((_n, t):tel) t2 = Pi (Inf t) (Inf (teleToITerm tel t2))
-- TODO
-- -- type check sized data type declarations.
-- typeCheckDeclaration :: Declaration -> TypeCheck ()
-- typeCheckDeclaration (DataDecl n sz tel t cs) =
--   do sig <- get
--      dt <- (teleToType tel t)
--      params <- length tel
--      p' <- (case sz of
--               Sized    -> params + 1
--               NotSized -> params)
--      checkDataType 0 [] [] p' dt
--       v <- whnf [] dt
--       put $ addSig sig n (DataSig params pos sz co v)
--       case sz of
--         Sized    -> szType params v
--         NotSized -> return ()
--       _ <- mapM (typeCheckConstructor n sz pos tel) cs
--       return () `throwTrace`
--   n
