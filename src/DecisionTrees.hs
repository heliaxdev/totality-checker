module DecisionTrees where
-- compiling function definitions with pattern matching to case trees
-- inspired by 
-- `Compiling Pattern Matching to Good Decision Trees` by Luc Maranget
import Types (Pattern(..), Value(..) )
import Data.Matrix --( Matrix(nrows, ncols), getRow, matrix, (<|>), submatrix )
import qualified Data.Vector as V --(Vector, notElem, map, head)
import Data.Vector.Mutable (swap)

-- in Data.Matrix the rows and cols start from 1
-- in Data.Vector the indexes start from 0

-- matrices of clauses: P -> A, where P is the pattern matrices. A is the rhs.
data ClauseMatrix
  = MkEmptyC
  | MkClauseMatrix (Matrix Pattern) (V.Vector Value)
  deriving (Show)

-- vertically joins 2 clause matrices
vJoin :: ClauseMatrix -> ClauseMatrix -> ClauseMatrix
vJoin (MkClauseMatrix p1 v1) (MkClauseMatrix p2 v2) =
  MkClauseMatrix ((<->) p1 p2) (v1 V.++ v2)
vJoin MkEmptyC c = c
vJoin c MkEmptyC = c

-- matrix decomposition operations: 
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
  -> Int -- the row to be checked
  -> ClauseMatrix -- the clause matrix to be transformed
  -- output is a matrix with some rows erased and some cols added
  -> ClauseMatrix
-- when the input clause matrix is empty, the specialized matrix is empty.
specialC _c _i MkEmptyC = MkEmptyC
specialC c@(ConP name listP) i clauseM@(MkClauseMatrix p v) 
  | i == nrows p + 1= MkEmptyC
  | otherwise =
      let makeCols = V.replicate (length listP)
          currentRow = getRow i p
          drop1Col = V.tail currentRow
          recurse = specialC c (i+1) clauseM
          returnClause v1 =
            vJoin 
              (MkClauseMatrix (rowVector (v1 V.++ drop1Col)) (V.slice (i-1) 1 v))
              recurse
      in
      case V.head currentRow of
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
              returnClause (V.fromList listPat)
        others ->
          errorMsg others
-- when the head constructor is a variable/wild card, the specialized matrix is empty.
specialC WildCardP _i _clauseMatrix = MkEmptyC
specialC (VarP _name) _i _clauseMatrix = MkEmptyC
specialC notVC _i _ =
  error $ "DecisionTrees, specialC: \n" 
    <> show notVC
    <> "\n is not a variable/constructor pattern. Cannot specialize." 

-- the default matrix retains the rows of P whose first pattern p_1^j admits all
-- values c'(v1,...va) as instances, where constructor c' is not present in the
-- first column of P.
defaultMatrix :: 
  ClauseMatrix -- the input clause matrix
  -> Int -- the row being checked
  -> ClauseMatrix -- the default matrix
defaultMatrix clauseM@(MkClauseMatrix p v) i
  | i == nrows p + 1 = MkEmptyC
  | otherwise =
      let recurse = defaultMatrix clauseM (i+1)
          returnVarP =
            vJoin 
              (MkClauseMatrix (rowVector (V.tail (getRow i p))) (V.slice (i-1) 1 v))
              recurse
      in
      case V.head (getRow i p) of
          WildCardP -> 
            returnVarP
          VarP _ -> returnVarP
          ConP _ _ -> vJoin MkEmptyC recurse
          others -> errorMsg others
-- when the input matrix is empty, the default matrix is empty.
defaultMatrix MkEmptyC _i = MkEmptyC

-- occurrences, sequences of integers that describe the positions of subterms.
data Occurrence
  = EmptyOccur Pattern -- empty occurrence
  | Occur Pattern Int -- an occurrence o followed by an Int k.
  deriving (Show)

extractPat :: Occurrence -> Pattern
extractPat (EmptyOccur pat) = pat
extractPat (Occur pat _n) = pat

-- target language
-- decision trees:

data DTree
  = Leaf Int -- success (k is an action) TODO transform b/t k and A?
  | Fail -- failure
  | Switch Occurrence [(Pattern, DTree)] -- multi-way test
  -- switch case lists are non-empty lists [(constructor, DTree)],
  | Swap Int DTree -- control instructions for evaluating decision trees

-- compilation scheme, takes 
-- (1) a vector of occurrences, oV
-- (2) a clause matrix, (P->A)
-- returns a DTree
cc :: 
  -- defines the fringe (the subterms of the subject value that  
  -- need to be checked against the patterns of P to decide matching)
  V.Vector Occurrence 
  -> ClauseMatrix
  -> DTree
cc _oV MkEmptyC = Fail -- if there's no pattern to match it fails.
cc oV clauseM@(MkClauseMatrix p a)
  | ncols p == 0 || -- if the number of column is 0 or
  -- if the first row of P has all wildcards 
    V.notElem 
      False 
      (V.map (== WildCardP) (getRow 1 p)) 
        = Leaf 1 -- then the first action is yielded.
  | otherwise = -- P has at least one row and at least one column and 
  -- in the first row, at least one pattern is not a wild card
      let firstCol = getCol 1 p
          ccSwitch occurSwitch clauseMSwitch =
            let headOccur = V.head occurSwitch
                tailOccur = V.tail occurSwitch
                cAPairList = 
                  V.toList (
                    V.map 
                      (\e -> 
                        -- map each constructor to a pair of head constr (HC) and
                        -- a decision tree of the specialized clause matrix of the HC 
                        (e, 
                        cc -- A_k = cc ((o_1 ·1 · · · o_1 ·a o_2 · · · o_n ), S(c_k , P → A))
                          (V.generate (arityC e) (Occur (extractPat headOccur)) V.++ tailOccur)
                          (specialC e 1 clauseMSwitch)))
                      firstCol)
            in
              -- the default matrix is only added when there exists a c 
              -- that is not in the first col. 
              if V.notElem (extractPat headOccur) firstCol then -- TODO confirm
                Switch 
                  headOccur
                  (
                    cAPairList <>
                    [ -- append *:A to the end of the list
                      (
                        ConP "default" [], -- constructor signalling default
                        cc tailOccur (defaultMatrix clauseMSwitch 1)
                      )
                    ]
                  )
              else
                Switch
                  headOccur
                  cAPairList
      in
        -- when i = 1 (col 1 has at least 1 pattern that is not a wild card)
        if findI p == 1 then
          ccSwitch oV clauseM
        else 
          -- when i /= 1, swap cols 1 and i in both the occurrence and P, 
          -- obtaining o' and p'. cc (o, (P->A)) = Swap i cc (o',(P'->A))
          let i = findI p
              o' = V.modify (\v -> swap v 0 (i-1)) oV
              p' = MkClauseMatrix (switchCols 1 i p) a
          in
            Swap i (ccSwitch o' p')

-- make sure to only use this 
-- when i cannot possibly be greater than the number of col of P
findIAux :: Int -> Matrix Pattern -> Int
findIAux i p =
  let whichCol col =
        any (/= WildCardP) (getCol col p)
  in
    if whichCol i then i
    else findIAux (i+1) p

findI :: Matrix Pattern -> Int
findI = findIAux 1
        
arityC :: Pattern -> Int
arityC (ConP _ listP) = length listP
arityC _ = 0

-- Functions for testing examples in GHCi
emptyList :: Pattern
emptyList = ConP "emptyList" []

consOp :: Pattern
consOp = ConP "cons" [WildCardP , WildCardP ]

test_p :: Matrix Pattern
test_p = fromLists [[emptyList, WildCardP], [WildCardP, emptyList], [consOp, consOp]]

test_p2 :: Matrix Pattern
test_p2 = fromLists [[emptyList, WildCardP], [WildCardP, emptyList], [WildCardP, WildCardP]]

test_a :: V.Vector Value
test_a = V.fromList [VGen 1, VGen 2, VGen 3]

pMtoA :: ClauseMatrix
pMtoA = MkClauseMatrix test_p2 test_a

test_oV :: V.Vector Occurrence
test_oV = V.fromList [EmptyOccur emptyList, EmptyOccur consOp]
