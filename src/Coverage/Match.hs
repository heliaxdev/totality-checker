{-| Matcher for coverage checking. Given

    1. the function clauses @cs@
    2. the patterns @ps@ of the split clause

we want to compute a variable index (in the split clause) to split on next.

The matcher here checks whether the split clause is covered by one of
the given clauses @cs@ or whether further splitting is needed (and
when yes, where).
-}

module Coverage.Match where

import Types

data Match a
  = Yes a
  | No
  | Block
    { blockedOnResult :: BlockedOnResult
    , blockedOnVars :: BlockingVars
    }

data BlockedOnResult
  = BlockedOnApply -- Blocked on un-introduced argument
  | NotBlockedOnResult

-- | Variable blocking a match
data BlockingVar = BlockingVar
  { blockingVarCons :: [Pattern] -- constructors in this position
  , blockingVarOverlap :: Bool 
  -- if at least one clause has a var pattern in this position
  }
  deriving (Show)

type BlockingVars = [BlockingVar]

-- | Match the given patterns against a list of clauses
-- if successful, return the index of the covering clause
-- calls matchClause which calls matchPat
-- match :: TypeCheck m 
--   => [Clause] -- search for clause that covers the patterns
--   -> SplitPattern -- patterns of the current splitClause
--   -> TypeCheck Nat
-- match cls pats = undefined

-- | @matchPat p q@ checks whether a function clause pattern @p@
--   covers a split clause pattern @q@.  There are three results:
--
--   1. @Yes rs@ means it covers, because @p@ is a variable pattern. @rs@ collects
--      the instantiations of the variables in @p@ s.t. @p[rs] = q@.
--
--   2. @No@ means it does not cover.
--
--   3. @Block [x]@ means @p@ is a proper instance of @q@ and could become
--      a cover if @q@ was split on variable @x@.

-- matchPat
--   :: (PureTCM m, DeBruijn a)
--   => Pattern' a
--      -- ^ Clause pattern @p@ (to cover split clause pattern).
--   -> SplitPattern
--      -- ^ Split clause pattern @q@ (to be covered by clause pattern).
--   -> m MatchResult
--      -- ^ Result.
--      --   If 'Yes', also the instantiation @rs@ of the clause pattern variables
--      --   to produce the split clause pattern, @p[rs] = q@.
-- matchPat p q = case p of

--   VarP _ x   -> yes [(fromMaybe __IMPOSSIBLE__ (deBruijnView x),q)]

--   DotP{}   -> yes []
--   ConP c ci ps -> unDotP q >>= unLitP >>= \case
--     VarP _ x -> blockedOnConstructor (splitPatVarIndex x) c ci
--     ConP c' i qs
--       | c == c'   -> matchPats ps qs
--       | otherwise -> no
--     DotP o t  -> no
--     DefP{}   -> no
--     LitP{}    -> __IMPOSSIBLE__  -- excluded by typing and unLitP
--     ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
--     IApplyP _ _ _ x -> blockedOnConstructor (splitPatVarIndex x) c ci

--   DefP o c ps -> unDotP q >>= \case
--     VarP _ x -> __IMPOSSIBLE__ -- blockedOnConstructor (splitPatVarIndex x) c
--     ConP c' i qs -> no
--     DotP o t  -> no
--     LitP{}    -> no
--     DefP o c' qs
--       | c == c'   -> matchPats ps qs
--       | otherwise -> no
--     ProjP{}   -> __IMPOSSIBLE__  -- excluded by typing
--     IApplyP _ _ _ x -> __IMPOSSIBLE__ -- blockedOnConstructor (splitPatVarIndex x) c

-- -- | Unfold one level of a dot pattern to a proper pattern if possible.
-- unDotP :: (MonadReduce m, DeBruijn a) => Pattern' a -> m (Pattern' a)
-- unDotP (DotP o v) = reduce v >>= \case
--   Var i [] -> return $ deBruijnVar i
--   Con c _ vs -> do
--     let ps = map (fmap $ unnamed . DotP o) $ fromMaybe __IMPOSSIBLE__ $ allApplyElims vs
--     return $ ConP c noConPatternInfo ps
--   Lit l -> return $ LitP (PatternInfo PatODot []) l
--   v     -> return $ dotP v
-- unDotP p = return p
