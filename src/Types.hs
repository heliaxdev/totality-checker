module Types where

import Control.Monad.State ( StateT )
import qualified Data.Map            as Map

data Expr
  = Star -- universe of small types
  | Var Name -- variable
  | Con Name -- constructor
  | Def Name -- function/data type
  | Lam Name Expr -- abstraction
  | Pi Name Expr Expr -- (PI) dependent function space
  | App Expr [Expr] -- application
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
  | VGen Int -- generic value k
  | VStar -- universe of small types
  | VCon Name -- constructor
  | VDef Name -- function/data
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

-- a clause has a list of patterns and the right hand side expression
data Clause =
  Clause [Pattern] Expr
  deriving (Eq, Show)

data Pattern
  = WildCardP -- wild card pattern
  | VarP Name -- variable pattern
  | ConP Name [Pattern] -- constructor pattern
  | DotP Expr -- inaccessible pattern
  | SuccP Pattern -- size successor pattern
  deriving (Eq, Show)

emptySig :: Signature
emptySig = Map.empty

lookupSig :: Name -> Signature -> SigDef
lookupSig n sig =
  case Map.lookup n sig of
    Nothing -> error $ "Error not in signature: " <> show n <> " " <> show sig
    Just k -> k

addSig :: Signature -> Name -> SigDef -> Signature
addSig sig n def = Map.insert n def sig

-- Return type of all type-checking functions.
-- state monad for global signature
type TypeCheck a = StateT Signature IO a
