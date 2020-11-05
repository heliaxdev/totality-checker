{- 
  Pattern coverage checking for function definitions. 
  Called by @typeCheckFunClause@ and @compileClauses@. 
  Result is a split tree. It's used to generate a case tree.
  In Coverage/, [Match.hs] transforms the patterns into a split tree.
  [SplitTree.hs] specifies what a split tree is.
-}

module Coverage where

import Types
import Coverage.Match
import Coverage.SplitTree

-- data SplitClause = SClause
--   { scTel    :: Telescope
--     -- ^ Type of variables in @scPats@.
--   , scPats   :: [NamedArg SplitPattern]
--     -- ^ The patterns leading to the currently considered branch of
--     --   the split tree.
--   , scSubst  :: Substitution' SplitPattern
--     -- ^ Substitution from 'scTel' to old context.
--     --   Only needed directly after split on variable:
--     --   * To update 'scTarget'
--     --   * To rename other split variables when splitting on
--     --     multiple variables.
--     --   @scSubst@ is not ``transitive'', i.e., does not record
--     --   the substitution from the original context to 'scTel'
--     --   over a series of splits.  It is freshly computed
--     --   after each split by 'computeNeighborhood'; also
--     --   'splitResult', which does not split on a variable,
--     --   should reset it to the identity 'idS', lest it be
--     --   applied to 'scTarget' again, leading to Issue 1294.
--   , scCheckpoints :: Map CheckpointId Substitution
--     -- ^ We need to keep track of the module parameter checkpoints for the
--     -- clause for the purpose of inferring missing instance clauses.
--   , scTarget :: Maybe (Dom Type)
--     -- ^ The type of the rhs, living in context 'scTel'.
--     --   'fixTargetType' computes the new 'scTarget' by applying
--     --   substitution 'scSubst'.
--   }

-- -- | A @Covering@ is the result of splitting a 'SplitClause'.
-- data Covering = Covering
--   { covSplitArg     :: Nat
--      -- ^ De Bruijn level (counting dot patterns) of argument we split on.
--   , covSplitClauses :: [(SplitTag, SplitClause)]
--       -- ^ Covering clauses, indexed by constructor/literal these clauses share.
--   }

-- -- | Project the split clauses out of a covering.
-- splitClauses :: Covering -> [SplitClause]
-- splitClauses (Covering _ qcs) = map snd qcs

-- -- | Create a split clause from a clause in internal syntax. Used by make-case.
-- clauseToSplitClause :: Clause -> SplitClause
-- clauseToSplitClause cl = SClause
--   { scTel    = clauseTel cl
--   , scPats   = toSplitPatterns $ namedClausePats cl
--   , scSubst  = idS  -- Andreas, 2014-07-15  TODO: Is this ok?
--   , scCheckpoints = Map.empty -- #2996: not __IMPOSSIBLE__ for debug printing
--   , scTarget = domFromArg <$> clauseType cl
--   }

-- | Top-level function for checking pattern coverage.
--
--   Effects:
--
--   - Marks unreachable clauses as such in the signature.
--
--   - Adds missing instances clauses to the signature.

coverageCheck :: (TypeSig, [Clause]) -> TypeCheck (SplitTree)
coverageCheck (TypeSig name rhs, cls) = undefined
