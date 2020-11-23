module Types where

import Control.Monad.State ( StateT )
import qualified Data.Map            as Map
import Data.Maybe (fromMaybe)

data Expr
  = Star -- universe of small types
  | Var Name -- variable
  | Con Name -- constructor
  | Def Name -- function/data type
  | Lam Name Expr -- abstraction
  | Pi Name Expr Expr -- (PI) dependent function space
  | App Expr [Expr] -- application
  | Refl -- proof of reflexivity
  -- size type for termination checking
  | Size -- size type
  | Succ Expr -- size successor
  | Infty -- size infinity (limit size)
  deriving (Show, Eq)

type Name = String

data Value
  = VApp Value [Value] -- application
  | VLam Name Env Expr -- Lam x e^ρ
  | VPi Name Value Env Expr -- Pi x v_A e^ρ where v_A = eval A^ρ
  -- atomic values:
  | VGen Int -- generic value k, starts from 0
  | VStar -- universe of small types
  | VCon Name -- constructor
  | VDef Name -- function/data
  | VRefl -- proof of reflexivity
  -- extensions for size type:
  | VSize -- size type
  | VInfty -- size limit
  | VSucc Value -- size successor
  deriving (Eq)

-- size successor: s infty = infty
sinfty :: Value -> Value
sinfty VInfty = VInfty
sinfty v      = VSucc v

instance Show Value where
  show VStar = "* "
  show (VLam name env e) =
    "(\\" <> show name <> " -> " <> showEnv env <> show e <> ")"
  show (VPi name ty env e) =
    "( " <> show name <> " : " <> show ty <> ") ->" <> showEnv env <> show e <>
    ")"
  show (VApp v vl) = "(" <> show v <> " " <> showVals vl <> ")"
  show (VCon name) = show name
  show (VDef name) = show name
  show (VGen k) = show k
  show VSize = "Size"
  show VInfty = "∞"
  show (VSucc s) = "(Size S " <> " " <> show s <> ")"
  show VRefl = "Refl"

showVals :: [Value] -> String
showVals []     = ""
showVals (v:vl) = show v <> " " <> showVals vl

showEnv :: Env -> String
showEnv [] = "{}"
showEnv x  = "{" <> showEnv' x <> "} "

showEnv' :: Env -> String
showEnv' [] = []
showEnv' ((n, v):env) = "(" <> show n <> " = " <> show v <> ")" <> showEnv' env

-- An environment (ρ) maps (free) variables to their types.
type Env = [(Name, Value)]

type Signature = Map.Map Name SigDef

data SigDef -- A signature is a mapping of constants to its info
  -- function constant to its type, clauses, whether it's type checked
  = FunSig Value [Clause] Bool
  | ConSig Value -- constructor constant to its type
  -- data type constant to # parameters, positivity of parameters, sized, type
  | DataSig Int [Pos] Sized Value
  deriving (Show)

data Pos -- positivity
  = SPos
  | NSPos
  deriving (Eq, Show)

data Sized -- distinguish between sized and not sized data type.
  = Sized
  | NotSized
  deriving (Eq, Show)

-- declarations are either (inductive) data types or functions
data Declaration
  -- a data declaration has a name,
  -- the positivity of its parameters,
  -- the telescope for its parameters,
  -- the expression,
  -- the list of constructors.
  = DataDecl Name Sized [Pos] Telescope Expr [TypeSig]
  -- a function declaration has a name, and an expression,
  -- and a list of clauses.
  | FunDecl [(TypeSig, [Clause])]
  deriving (Eq, Show)

data TypeSig =
  TypeSig Name Expr
  deriving (Eq, Show)

-- A telescope is a sequence of types where
-- later types may depend on elements of previous types.
-- Used for parameters of data type declarations.
type Telescope = [TBind]

type TBind = (Name, Expr)

-- | A clause is a list of patterns and the clause body.
--
--  The telescope contains the types of the pattern variables and the
--  de Bruijn indices say how to get from the order the variables occur in
--  the patterns to the order they occur in the telescope. The body
--  binds the variables in the order they appear in the telescope.
--
--  @clauseTel ~ permute clausePerm (patternVars namedClausePats)@
--
--  Terms in dot patterns are valid in the clause telescope.
--
--  For the purpose of the permutation and the body dot patterns count
--  as variables. TODO: Change this!
data Clause = Clause
    { clauseTel       :: Telescope
      -- ^ @Δ@: The types of the pattern variables in dependency order.
    -- , namedClausePats :: NAPs (Using Name instead atm)
      -- ^ @Δ ⊢ ps@.  The de Bruijn indices refer to @Δ@.
    , namedClausePats :: [SplitPattern]
    , clauseBody      :: Maybe Expr
      -- ^ @Just v@ with @Δ ⊢ v@ for a regular clause, or @Nothing@ for an
      --   absurd one.
    , clauseType      :: Maybe Value
      -- ^ @Δ ⊢ t@.  The type of the rhs under @clauseTel@.
    , clauseCatchall  :: Bool
      -- ^ Clause has been labelled as CATCHALL.
    -- , clauseRecursive   :: Maybe Bool TODO add this when termination checking
      -- ^ @clauseBody@ contains recursive calls; computed by termination checker.
      --   @Nothing@ means that termination checker has not run yet,
      --   or that @clauseBody@ contains meta-variables;
      --   these could be filled with recursive calls later!
      --   @Just False@ means definitely no recursive call.
      --   @Just True@ means definitely a recursive call.
    , clauseUnreachable :: Maybe Bool
      -- ^ Clause has been labelled as unreachable by the coverage checker.
      --   @Nothing@ means coverage checker has not run yet (clause may be unreachable).
      --   @Just False@ means clause is not unreachable.
      --   @Just True@ means clause is unreachable.
    }
  deriving (Eq, Show)
  
-- | Type used when numbering pattern variables.
data DBPatVar = DBPatVar
  { dbPatVarName  :: Name
  , dbPatVarIndex :: Int
  } deriving (Show, Eq)

data Pattern
  = WildCardP -- wild card pattern
  -- | LiteralP Literal -- literal pattern TODO
  | VarP Name -- variable pattern
  | ConP Name [SplitPattern] -- constructor pattern
  | DotP Expr -- forced/inaccessible pattern
  | AbsurdP -- absurd pattern
  | SuccP Pattern -- size successor pattern
  deriving (Eq, Show)
-- A variable in the pattern of a split clause
data SplitPattern = SplitPatVar
  { splitPatVar :: Pattern -- the pattern (with names)
  , splitPatVarIndex :: Int -- the de Bruijn index of the variable
  -- , splitExcludedLits :: [Literal] TODO the literals excluded by previous matches.    
  }
  deriving (Eq, Show)
  
clToPatL :: Clause -> [Pattern]
clToPatL cl = map splitPatVar (namedClausePats cl)

splitPatsToPats :: [SplitPattern] -> [Pattern]
splitPatsToPats = map splitPatVar

emptySig :: Signature
emptySig = Map.empty

lookupSig :: Name -> Signature -> SigDef
lookupSig n sig =
  fromMaybe
    (error $ 
      "lookupSig: " <> show n <> " not in signature " <> show sig)
    (Map.lookup n sig)

addSig :: Signature -> Name -> SigDef -> Signature
addSig sig n def = Map.insert n def sig

-- Return type of all type-checking functions.
-- state monad for global signature
type TypeCheck a = StateT Signature IO a
