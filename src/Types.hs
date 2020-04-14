module Types where

import           Control.Monad.State
import qualified Data.Map            as Map

data Expr
  = Star -- universe of small types
  | Var Name -- variable
  | Con Name -- constructor name
  | Def Name -- function/data type name
  | Lam Name Expr -- abstraction
  | Pi Name Expr Expr -- (PI) dependent function space
  | App Expr [Expr] -- application
  -- size type for termination checking
  | Size -- size type
  | SuccS Expr -- size successor
  | Infty -- size infinity (limit size)
  deriving (Show, Eq)

data Name =
  String
  deriving (Show, Eq, Ord)

data Value
  = VStar
  | VApp Value [Value]
  | VCon Name
  | VDef Name
  | VLam Name Env Expr
  | VPi Name Value Env Expr
  -- generic value (k of type nat): the computed value of a variable during
  -- type-checking.
  | VGen Int
  -- extensions for size type
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

-- Environment maps variables to their types.
type Env = [(Name, Value)]

type Signature = Map.Map Name SigDef

data SigDef
  = FunSig Value [Clause] Bool --type, clauses, whether it's type checked
  | DataSig Int [Pos] Sized Value -- # parameters, positivity of parameters, sized, type
  deriving (Show)

data Pos -- positivity
  = SPos
  | NSPos
  deriving (Eq, Show)

data Sized -- distinguish between sized and not sized data type.
  = Sized
  | NotSized
  deriving (Eq, Show)

data Declaration
  = DataDecl Name Sized [Pos] Telescope Type [Constructor]
  | FunDecl [(TypeSig, [Clause])]
  deriving (Eq, Show)

data TypeSig =
  TypeSig Name Type
  deriving (Eq, Show)

type Type = Expr

type Constructor = TypeSig

type TBind = (Name, Type)

type Telescope = [TBind]

data Clause =
  Clause [Pattern] Expr
  deriving (Eq, Show)

data Pattern
  = VarP Name
  | ConP Name [Pattern]
  | SuccP Pattern
  | DotP Expr
  deriving (Eq, Show)

teleToType :: Telescope -> Type -> Type
teleToType [] t            = t
teleToType ((n, t):tel) t2 = Pi n t (teleToType tel t2)

splitTeleType :: Int -> (Telescope, Type) -> (Telescope, Type)
splitTeleType 0 (tel, t)         = (tel, t)
splitTeleType k (tel, Pi n t t2) = splitTeleType (k - 1) (tel <> [(n, t)], t2)

typeToTele :: Type -> (Telescope, Type)
typeToTele t = ttt t []
  where
    ttt :: Type -> Telescope -> (Telescope, Type)
    ttt (Pi n t' t2) tel = ttt t2 (tel <> [(n, t')])
    ttt x tel            = (tel, x)

emptySig = Map.empty

lookupSig :: Name -> Signature -> SigDef
lookupSig n sig =
  case Map.lookup n sig of
    Nothing -> error $ "Error not in signature: " <> show n <> " " <> show sig
    Just k -> k

-- fromMaybe
--     (error $ "Error not in signature: " <> n <> " " <> show sig)
--     (Map.lookup n sig)
addSig :: Signature -> Name -> SigDef -> Signature
addSig sig n def = Map.insert n def sig

-- state monad for global signature
type TypeCheck a = StateT Signature IO a
