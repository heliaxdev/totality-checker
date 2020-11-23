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
import qualified Data.List as List
import GHC.Base (Nat)
data Match a
  = Yes a -- (MATCH) -- the current neighbourhood matches a clause
  | No -- (MISSED) -- the current neighbourhood fails to match all clauses
  | Block -- (SPLIT) -- matching inconclusive
    { blockedOnResult :: BlockedOnResult
    , blockedOnVars :: BlockingVars
    }
  deriving (Show)

type SplitInstantiation = [(Nat, SplitPattern)]
data BlockedOnResult
  = BlockedOnApply -- Blocked on un-introduced argument
  | NotBlockedOnResult
  deriving (Show)

-- | Variable blocking a match
data BlockingVar = BlockingVar
  { blockingVarName :: Maybe Name -- name of variable blocking the match
    -- Nothing when it's a no name var/wildcard (TODO Will this be a problem?)
  , blockingVarCons :: [Pattern] -- constructors in this position
  , blockingVarOverlap :: Bool 
  -- if at least one clause has a var pattern in this position
  }
  deriving (Show)

type BlockingVars = [BlockingVar]

-- | @choice m m'@ combines the match results @m@ of a function clause
--   with the (already combined) match results $m'$ of the later clauses.
--   It is for skipping clauses that definitely do not match ('No').
--   It is left-strict, to be used with @foldr@.
--   If one clause unconditionally matches ('Yes') we do not look further.
choice :: Match a -> Match a -> Match a
choice m m' = case m of
  Yes a -> Yes a
  Block r xs -> case m' of
    Block s ys -> Block (choiceBlockedOnResult r s) $ zipBlockingVars xs ys
    Yes _      -> Block r $ overlapping xs
    No         -> Block r xs
  No    -> m'

setBlockingVarOverlap :: BlockingVar -> BlockingVar
setBlockingVarOverlap = \x -> x { blockingVarOverlap = True }
  
overlapping :: BlockingVars -> BlockingVars
overlapping = map setBlockingVarOverlap
  
-- | Left dominant merge of blocking vars.
zipBlockingVars :: BlockingVars -> BlockingVars -> BlockingVars
zipBlockingVars xs ys = map upd xs
  where
    upd (BlockingVar name cons o) = 
      case List.find ((name ==) . blockingVarName) ys of
        Just (BlockingVar _ cons' o') -> BlockingVar name (cons ++ cons') (o || o')
        Nothing -> BlockingVar name cons True

-- | Left dominant merge of `BlockedOnResult`.
choiceBlockedOnResult :: BlockedOnResult -> BlockedOnResult -> BlockedOnResult
choiceBlockedOnResult b1 b2 = case (b1,b2) of
  (NotBlockedOnResult  , _                 ) -> NotBlockedOnResult
  (BlockedOnApply    , _                 ) -> BlockedOnApply

-- | @matchClause qs i c@ checks whether clause @c@
--   covers a split clause with patterns @qs@.
matchClause ::
  [SplitPattern]
     -- ^ Split clause patterns @qs@.
  -> Clause
     -- ^ Clause @c@ to cover split clause.
  -> Match SplitInstantiation
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @(namedClausePats c)[rs] == qs@.
matchClause qs cl = matchPats (clToPatL cl) qs

-- | Match the given patterns against a list of clauses
-- if successful, return the index of the covering clause
-- called by @cover@ in [Coverage.hs]
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

matchPat ::
  Pattern
  -- ^ Clause pattern @p@ (to cover split clause pattern).
  -> SplitPattern
     -- ^ Split clause pattern @q@ (to be covered by clause pattern).
  -> Match SplitInstantiation
     -- ^ Result.
     --   If 'Yes', also the instantiation @rs@ of the clause pattern variables
     --   to produce the split clause pattern, @p[rs] = q@.
matchPat p q = case p of
  WildCardP -> Yes [(undefined,q)]
  VarP _   -> Yes [(undefined,q)]
  DotP _ -> Yes []
  AbsurdP -> No -- AbsurdP will never be matched
  SuccP _ -> error $ "matchPat: the user cannot enter SuccP as a pattern" 
  ConP name pats -> case splitPatVar q of 
    -- unDotP q >>= \case TODO undot a level
    WildCardP -> Block NotBlockedOnResult [BlockingVar Nothing [] False]
    VarP vname -> Block NotBlockedOnResult [BlockingVar (Just vname) [] False]
    ConP qname qs
      | name == qname -> 
          matchPats 
            pats 
            [SplitPatVar (ConP qname qs) (splitPatVarIndex q)] 
            -- TODO ^is this right? Should each of the pat in qs
            -- be a SplitPatVar?
      | otherwise -> No
    DotP _ -> No
    AbsurdP -> No
    SuccP _ -> error $ "matchPat: SuccP is not a suitable pattern."
  
-- | Unfold one level of a dot pattern to a proper pattern if possible.
-- unDotP :: (MonadReduce m, DeBruijn a) => Pattern -> m Pattern
-- unDotP (DotP v) = reduce v >>= \case
--   Var i [] -> return $ deBruijnVar i
--   Con c _ vs -> do
--     let ps = map (fmap $ unnamed . DotP o) $ fromMaybe __IMPOSSIBLE__ $ allApplyElims vs
--     return $ ConP c noConPatternInfo ps
--   Lit l -> return $ LitP (PatternInfo PatODot []) l
--   v     -> return $ dotP v
-- unDotP p = return p

-- | @matchPats ps qs@ checks whether a function clause with patterns
--   @ps@ covers a split clause with patterns @qs@.
matchPats ::
  [Pattern]
     -- ^ Clause pattern vector @ps@ (to cover split clause pattern vector).
  -> [SplitPattern]
     -- ^ Split clause pattern vector @qs@ (to be covered by clause pattern vector).
  -> Match SplitInstantiation
     -- ^ Result.
     --   If 'Yes' the instantiation @rs@ such that @ps[rs] == qs@.
matchPats [] [] = Yes []
matchPats (p:ps) (q:qs) =
  matchPat p q `combine` matchPats ps qs
matchPats [] (_:_) = Yes []
matchPats (_p:_ps) [] = Block BlockedOnApply []

-- | Combine results of checking whether function clause patterns
--   covers split clause patterns.
--
--   'No' is dominant: if one function clause pattern doesn't match then
--   the whole clause doesn't match.
--
--   'Yes' is neutral: for a match, all patterns have to match.
--
--   'Block' accumulates variables of the split clause
--   that have to be instantiated
--   to make the split clause an instance of the function clause.
combine :: 
  Match SplitInstantiation -> Match SplitInstantiation -> Match SplitInstantiation
combine m m' = case m of
    Yes a -> case m' of
      Yes b -> Yes (a <> b)
      noOrBlock     -> noOrBlock
    No    -> No
    x@(Block r xs) -> case m' of
      No    -> No
      Block s ys -> Block (anyBlockedOnResult r s) (xs ++ ys)
      Yes _ -> x

anyBlockedOnResult :: BlockedOnResult -> BlockedOnResult -> BlockedOnResult
anyBlockedOnResult b1 b2 = case (b1, b2) of
  (NotBlockedOnResult, b2') -> b2'
  (b1', NotBlockedOnResult) -> b1'
  _ -> error $ 
        "anyBlockedOnResult: Impossible " <> show b1 <> " and " <> show b2