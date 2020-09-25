module DecisionTrees where
-- compiling function definitions with pattern matching to case trees
-- inspired by 
-- `Compiling Pattern Matching to Good Decision Trees` by Luc Maranget
import Types (Pattern,  Value )
import Data.Matrix

-- matrices of clauses: P -> A, where P is the pattern matrices.
-- matrix decomposition operations: 
-- (1) specialization by a constructor c, S(c,P->A) 
-- (2) computation of the default matrix, D(P->A)

-- specialization by constructor c simplifies matrix P under the assumption that
-- v1 admits c as a head constructor.

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
  = Leaf Int -- success (k is an action)
  | Fail -- failure
  | Switch Occurrence [(Value, DTree)] -- multi-way test
  -- switch case lists are non-empty lists [(constructor, DTree)],
  | Swap Int DTree -- control instructions for evaluating decision trees

-- compilation scheme, takes 
-- (1) a vector of occurrences, oV
-- (2) a clause matrix, clauseM
cc :: [Occurrence] -> (Matrix Pattern -> [Value]) -> DTree
cc = undefined