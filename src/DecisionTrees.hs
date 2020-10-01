module DecisionTrees where
-- compiling function definitions with pattern matching to case trees
-- inspired by 
-- `Compiling Pattern Matching to Good Decision Trees` by Luc Maranget
import Types (Pattern(..), Value )
import Data.Matrix --( Matrix(nrows, ncols), getRow, matrix, (<|>), submatrix )
import qualified Data.Vector as V --(Vector, notElem, map, head)

-- matrices of clauses: P -> A, where P is the pattern matrices. A is the rhs.
data ClauseMatrix
  = MkClauseMatrix (Matrix Pattern) (V.Vector Value)

vJoin :: ClauseMatrix -> ClauseMatrix -> ClauseMatrix
vJoin (MkClauseMatrix p1 v1) (MkClauseMatrix p2 v2) =
  MkClauseMatrix ((<->) p1 p2) (v1 V.++ v2)

-- matrix decomposition operations: 
-- (1) specialization by a constructor c, S(c,P->A) 
-- (2) computation of the default matrix, D(P->A)

-- specialization by constructor c simplifies matrix P under the assumption that
-- v1 admits c as a head constructor. (See p.3 of paper)
specialC :: 
  Pattern -- specialization by this constructor (c)
  -> Int -- the row to be checked
  -> ClauseMatrix -- the clause matrix to be transformed
  -- output is a matrix with some rows erased and some cols added
  -> ClauseMatrix
specialC c@(ConP name listP) i clauseM@(MkClauseMatrix p v) =
  let firstRow = getRow i p in -- currently building the i-th row 
  case V.head firstRow of
    WildCardP -> -- when p_1^j is a wild card, add wild card cols to the row
      let wildCardCols = 
            -- the no. of cols to add equals the no. of constructor args
            V.generate (length listP) (const WildCardP)
          dropped1Col = -- drop the first col of the original row
            V.slice 2 (ncols p - 1) firstRow
      in
        vJoin 
          (MkClauseMatrix (rowVector (wildCardCols V.++ dropped1Col)) (V.take i v))
          (specialC c (i+1) clauseM) -- TODO i needs to be less than nrows p
    (ConP nameC listPat) -> undefined
    _ -> undefined


-- the default matrix retains the rows of P whose first pattern p_1^j admits all
-- values c'(v1,...va) as instances, where constructor c' is not present in the
-- first column of P.

-- occurrences, sequences of integers that describe the positions of subterms.
data Occurrence
  = Empty -- empty occurrence
  | Occur Int Int -- k followed by an occurrence o

-- target language
-- decision trees:

data DTree
  = Leaf Int -- success (k is an action) TODO transform b/t k and A?
  | Fail -- failure
  | Switch Occurrence [(Value, DTree)] -- multi-way test
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
cc oV (MkClauseMatrix p a)
  | nrows p == 0 = Fail -- if there's no pattern to match it fails.
  | ncols p == 0 || -- if the number of column is 0 or
  -- if the first row of P has all wildcards 
    V.notElem 
      False 
      (V.map (== WildCardP) (getRow 1 p)) 
        = Leaf 1 -- then the first action is yielded.
  | otherwise = -- P has at least one row and at least one column and 
  -- in the first row, at least one pattern is not a wild card
      compiles oV (MkClauseMatrix p a)

compiles :: V.Vector Occurrence 
  -> ClauseMatrix
  -> DTree
compiles oV (MkClauseMatrix p a) = undefined