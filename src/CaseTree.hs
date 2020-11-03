{-# LANGUAGE TupleSections #-}
module CaseTree where

import Types (Expr, Clause, TypeCheck)

-- | Process function clauses into case tree.
--   This involves:
--   1. Coverage checking, generating a split tree.
--   2. Translation of lhs record patterns into rhs uses of projection.
--      Update the split tree.
--   3. Generating a case tree from the split tree.
--   Phases 1. and 2. are skipped if @Nothing@.

compileClauses ::
  Maybe (QName, Type) -- ^ Translate record patterns and coverage check with given type?
  -> [Clause]
  -> TypeCheck (Maybe SplitTree, CompiledClauses)
compileClauses mt cs =
-- Construct clauses with pattern variables bound in left-to-right order.
-- Discard de Bruijn indices in patterns.
  case mt of
    Nothing -> (Nothing,) . compile . map unBruijn <$> cs
    Just (q, t)  -> do
      splitTree <- coverageCheck q t cs
      -- The coverage checker might have added some clauses!
      -- Throw away the unreachable clauses.
      let notUnreachable = (Just True /=) . clauseUnreachable
      cs <- normaliseProjP =<< instantiateFull =<< filter notUnreachable . defClauses <$> getConstInfo q
      let cls = map unBruijn cs
      let cc = compileWithSplitTree splitTree cls
      (cc,_) <- runChangeT $ translateCompiledClauses cc
      return (Just splitTree, cc)

data WithArity c = WithArity { arity :: Int, content :: c }
  deriving (Data, Functor, Foldable, Traversable, Show)

-- | Branches in a case tree.

type SplitTree  = SplitTree'  SplitTag
type SplitTrees = SplitTrees' SplitTag

-- | Tag for labeling branches of a split tree. Each branch is associated to
--   either a constructor or a literal, or is a catchall branch (currently
--   only used for splitting on a literal type).
data SplitTag
  = SplitCon QName
  | SplitLit Literal
  | SplitCatchall
  deriving (Show, Eq, Ord, Data)

data Case c = Branches
  { conBranches    :: Map QName (WithArity c)
    -- ^ Map from constructor names to their arity
    --   and the case subtree.
  , etaBranch      :: Maybe (ConHead, WithArity c)
    -- ^ Eta-expand with the given (eta record) constructor. If this is
    --   present, there should not be any conBranches or litBranches.
  , litBranches    :: Map Literal c
    -- ^ Map from literal to case subtree.
  , catchAllBranch :: Maybe c
    -- ^ (Possibly additional) catch-all clause.
  , fallThrough :: Maybe Bool
    -- ^ (if True) In case of non-canonical argument use catchAllBranch.
  }
  deriving (Data, Functor, Foldable, Traversable, Show)

-- | Case tree with bodies.

data CompiledClauses' a
  = Case Int (Case (CompiledClauses' a))
    -- ^ @Case n bs@ stands for a match on the @n@-th argument
    -- (counting from zero) with @bs@ as the case branches.
  | Done [Arg ArgName] a
    -- ^ @Done xs b@ stands for the body @b@ where the @xs@ contains hiding
    --   and name suggestions for the free variables. This is needed to build
    --   lambdas on the right hand side for partial applications which can
    --   still reduce.
  | Fail
    -- ^ Absurd case.
  deriving (Data, Functor, Traversable, Foldable, Show)

type CompiledClauses = CompiledClauses' Expr

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
  deriving (Data, Show)

-- | Split tree branching.  A finite map from constructor names to SplitTrees
--   A list representation seems appropriate, since we are expecting not
--   so many constructors per data type, and there is no need for
--   random access.
type SplitTrees' a = [(a, SplitTree' a)]
  