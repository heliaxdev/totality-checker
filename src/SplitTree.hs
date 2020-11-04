{-| Split tree for transforming pattern clauses into case trees.

The coverage checker [Coverage.hs] generates a split tree from the clauses.
The clause compiler [CaseTree.hs] uses it to transform clauses to case trees.

The initial problem is a set of clauses.  The root node designates
on which argument to split and has subtrees for all the constructors.
Splitting continues until there is only a single clause left at
each leaf of the split tree.

-}

module SplitTree where

import Types ( Name )
  
-- | Branches in a case tree.

type SplitTree  = SplitTree'  SplitTag
type SplitTrees = SplitTrees' SplitTag

-- | Tag for labeling branches of a split tree. Each branch is associated to
--   either a constructor or a literal, or is a catchall branch (currently
--   only used for splitting on a literal type).
data SplitTag
  = SplitCon Name
  deriving (Show)
-- | SplitLit Literal TODO?
-- | SplitCatchall
  
-- | Abstract case tree shape.
data SplitTree' a
  = -- | No more splits coming. We are at a single, all-variable
    -- clause.
    SplittingDone
    { splitBindings :: Int       -- ^  The number of variables bound in the clause
    }
  | -- | A split is necessary.
    SplitAt
    { splitArg   :: Int       -- ^ Arg. no to split at.
    , splitTrees :: SplitTrees' a -- ^ Sub split trees.
    }
  deriving (Show)

-- | Split tree branching.  A finite map from constructor names to SplitTrees
--   A list representation seems appropriate, since we are expecting not
--   so many constructors per data type, and there is no need for
--   random access.
type SplitTrees' a = [(a, SplitTree' a)]
  