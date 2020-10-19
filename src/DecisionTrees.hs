module DecisionTrees where
-- compiling function definitions with pattern matching to case trees
-- inspired by 
-- `Compiling Pattern Matching to Good Decision Trees` by Luc Maranget
-- implemented using list of lists instead of matrix so that clauses can 
-- have different number of args
import Types (Pattern(..), Value(..) )
import Data.List ( unfoldr )
-- A function definition can be represented as P -> A, 
-- where P is the list of clauses, and each clause contains a list of patterns.
-- A is the list of rhs of the clauses.
data ClauseList
  = MkEmptyC
  | MkClauseList [[Pattern]] [Value]
  deriving (Show)

-- vertically joins 2 clause matrices
vJoin :: ClauseList -> ClauseList -> ClauseList
vJoin (MkClauseList p1 v1) (MkClauseList p2 v2) =
  MkClauseList (p1 <> p2) (v1 <> v2)
vJoin MkEmptyC c = c
vJoin c MkEmptyC = c

-- decomposition operations: 
-- (1) specialization by a constructor c, S(c,P->A) 
-- (2) computation of the default matrix, D(P->A)

errorMsg :: Show a1 => a1 -> a2
errorMsg pat =
  error $ 
    "DecisionTrees, specialC: \n" 
    <> show pat
    <> "\n is not a valid pattern to match." 
    <> " Expecting a wild card, variable or constructor patterns." 

-- specialization by constructor c simplifies matrix P under the assumption that
-- v1 admits c as a head constructor. (See p.3 of paper)
specialC :: 
  Pattern -- specialization by this constructor (c), aka the head constructor
  -> ClauseList -- the clause matrix to be transformed
  -- output is a matrix with some rows erased and some cols added
  -> ClauseList
-- when the input clause matrix is empty, the specialized matrix is empty.
specialC _c MkEmptyC = MkEmptyC
specialC c@(ConP name listP) (MkClauseList (hdp:tlp) (hda:tla)) =
  let makeCols = replicate (length listP)
      drop1Col = tail hdp
      recurse = specialC c (MkClauseList tlp tla)
      returnClause pats =
        vJoin 
          (MkClauseList [pats <> drop1Col] [hda])
          recurse
  in
    case head hdp of
      WildCardP -> 
        -- when p_1^j is a wild card, add wild card cols to the row
        -- the no. of cols to add equals the no. of constructor args
        returnClause (makeCols WildCardP)
      VarP nameV -> returnClause (makeCols $ VarP nameV)
      (ConP nameC listPat) 
        -- when the constructor names are not the same, no row
        | nameC /= name -> 
            vJoin
              MkEmptyC
              recurse
        | otherwise -> -- when the constructor names are the same
            -- add the constructor argument cols in front
            returnClause listPat
      others ->
        errorMsg others
-- when the head constructor is a variable/wild card, the specialized matrix is empty.
specialC WildCardP _clauseL = MkEmptyC
specialC (VarP _name) _clauseL = MkEmptyC
specialC notVC _ =
  error $ "DecisionTrees, specialC: \n" 
    <> show notVC
    <> "\n is not a variable/constructor pattern. Cannot specialize." 
  
lhsEmpty :: Show a => [a] -> String -- for error msg
lhsEmpty rhs = 
  "the number of clauses on the left and right hand side are not equal."
  <> " The left hand side of the function clauses is empty,"
  <> " while the right hand side is "
  <> show rhs

rhsEmpty :: Show a => [a] -> String -- for error msg
rhsEmpty lhs = 
  "the number of clauses on the left and right hand side are not equal."
  <> " The right hand side of the function clauses is empty,"
  <> " while the left hand side is "
  <> show lhs

-- the default matrix retains the rows of P whose first pattern p_1^j admits all
-- values c'(v1,...va) as instances, where constructor c' is not present in the
-- first column of P.
defaultMatrix :: 
  ClauseList -- the input clause matrix
  -> ClauseList -- the default matrix
-- when the input matrix is empty, the default matrix is empty.
defaultMatrix MkEmptyC = MkEmptyC
defaultMatrix (MkClauseList [] a) = error $
  "DecisionTrees, defaultMatrix: "
  <> lhsEmpty a
defaultMatrix (MkClauseList p []) = error $
  "DecisionTrees, defaultMatrix: "
  <> rhsEmpty p
defaultMatrix (MkClauseList (hdp:tlp) (hda:tla)) =
  let recurse = defaultMatrix (MkClauseList tlp tla)
      returnVarP =
        vJoin 
          (MkClauseList [tail hdp] [hda])
          recurse
  in
  case head hdp of
      WildCardP -> 
        returnVarP
      VarP _ -> returnVarP
      ConP _ _ -> vJoin MkEmptyC recurse
      others -> errorMsg others

-- occurrences, sequences of integers that describe the positions of subterms.
data Occurrence
  = EmptyOccur -- empty occurrence
  | Occur Int Occurrence -- an Int k followed by an occurrence o.
  deriving (Show)

-- target language
-- decision trees:

data DTree
  = Leaf Int -- success (k is an action) TODO transform b/t k and A?
  | Fail -- failure
  | Switch Occurrence [(Pattern, DTree)] -- multi-way test
  -- switch case lists are non-empty lists [(constructor, DTree)],
  | Swap Int DTree -- control instructions for evaluating decision trees

-- compilation scheme, takes 
-- (1) a list of occurrences, oL
-- (2) a clause list, (P->A)
-- returns a DTree
cc :: 
  -- defines the fringe (the subterms of the subject value that  
  -- need to be checked against the patterns of P to decide matching)
  [Occurrence] 
  -> ClauseList
  -> DTree
cc _oL MkEmptyC = Fail -- if there's no pattern to match it fails.
cc _oL (MkClauseList [] a) = error $
  "DecisionTrees, cc: "
  <> lhsEmpty a
cc _oL (MkClauseList p []) = error $
  "DecisionTrees, cc: "
  <> rhsEmpty p
cc oL clauseL@(MkClauseList p@(hdp:_) _)
  | all (== 0) (map length p) || -- if the number of column is 0 or
  -- if the first row of P has all wildcards 
    all (== WildCardP) hdp 
        = Leaf 1 -- then the first action is yielded.
  | otherwise = -- P has at least one row and at least one column and 
  -- in the first row, at least one pattern is not a wild card
      let firstCol = map head p
          ccSwitch occurSwitch clauseMSwitch =
            let headOccur = head occurSwitch
                tailOccur = tail occurSwitch
                cAPairList = -- [c_1;A_1...c_z;A_z]
                    map 
                      (\e -> 
                        -- map each constructor to a pair of head constr (HC)
                        -- and a decision tree of the specialized clause matrix
                        -- of the HC
                        (e, 
                        cc 
                        -- A_k = 
                        -- cc ((1·o_1 · · · a·o_1   o_2 · · · o_n ), S(c_k , P → A))
                          (
                            unfoldr 
                              (\b -> 
                                if b+1 == arityC e then 
                                  Nothing 
                                else Just (Occur b headOccur, b+1)
                              ) 
                              1
                            <> tailOccur
                          )
                          (specialC e clauseMSwitch)))
                      firstCol
            in
              -- the default matrix is only added when there exists a 
              -- constructor that is not in the first col. So, if there is
              -- pattern matching coverage check, it's never added. 
              if False then -- TODO: if the first col does not form a sig
                Switch 
                  headOccur
                  (
                    cAPairList <>
                    [ -- append *:A to the end of the list
                      (
                        ConP "default" [], -- constructor signalling default
                        cc tailOccur (defaultMatrix clauseMSwitch)
                      )
                    ]
                  )
              else -- the 1st col is a sig (1st col has all the constructors)
                Switch
                  headOccur
                  cAPairList
      in
        -- when i = 1 (col 1 has at least 1 pattern that is not a wild card)
        if any (/= WildCardP) (map head p) then
          ccSwitch oL clauseL
        else 
          -- if first col has all wildcards then there must be more than 1 col
          -- otherwise it will return Leaf 1
          -- when i /= 1, swap cols 1 and i in both the occurrence and P, 
          -- obtaining o' and p'. cc (o, (P->A)) = Swap i cc (o',(P'->A))
          undefined -- TODO this may be problematic with dependent pat matching?

arityC :: Pattern -> Int
arityC (ConP _ listP) = length listP
arityC _ = 0

-- Functions for testing examples in GHCi
emptyList :: Pattern
emptyList = ConP "emptyList" []

consOp :: Pattern
consOp = ConP "cons" [WildCardP , WildCardP ]

test_p :: [[Pattern]]
test_p = [[emptyList, WildCardP], [WildCardP, emptyList], [consOp, consOp]]

test_p2 :: [[Pattern]]
test_p2 = [[emptyList, WildCardP], [WildCardP, emptyList], [WildCardP, WildCardP]]

test_a :: [Value]
test_a = [VGen 1, VGen 2, VGen 3]

pMtoA :: ClauseList
pMtoA = MkClauseList test_p2 test_a

test_oV :: [Occurrence]
test_oV = [EmptyOccur, Occur 1 EmptyOccur]
