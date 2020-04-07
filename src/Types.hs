module Types where

data ITerm -- Inferable terms
  = Ann CTerm CTerm -- annotated terms
  | Star -- (STAR) Star (the type of types) is now a term
  | Pi CTerm CTerm -- (PI) dependent function space
  | Bound Int -- Bound variables of type Int because it's represented by de Bruijn indices
  | Free Name -- Free variables of type name (see below)
  | App ITerm CTerm -- application
  | Nat -- Nat data type
  | Zero -- data constructor of Nat
  | Succ CTerm -- data constructor of Nat
  | NatElim CTerm CTerm CTerm CTerm -- eliminator of Nat
  | Vec CTerm CTerm -- Vec (vector) data type
  | Nil CTerm -- data constructor of Vec
  | Cons CTerm CTerm CTerm CTerm -- data constructor of Vec
  | VecElim CTerm CTerm CTerm CTerm CTerm CTerm -- eliminator of Vec
  | Eq CTerm CTerm CTerm -- Eq (equality) data type
  | Refl CTerm CTerm -- data constructor of Eq
  | EqElim CTerm CTerm CTerm CTerm CTerm CTerm -- eliminator of Eq
  -- size type for termination checking
  | Size -- size type
  | SuccS CTerm -- size successor
  | Infty -- size infinity (limit size)
  deriving (Show, Eq)

data CTerm --Checkable terms
  = Inf ITerm --(CHK) Inf is the constructor that embeds ITerm to CTerm
  | Lam CTerm --(LAM) Lam stands for Lambda abstractions
  deriving (Show, Eq)
  --Helper functions for turning ITerms to CTerm

cStar :: CTerm
cStar = Inf Star

cPi :: CTerm -> CTerm -> CTerm
cPi f t = Inf (Pi f t)

cBound :: Int -> CTerm
cBound x = Inf (Bound x)

cNat :: CTerm
cNat = Inf Nat

cZero :: CTerm
cZero = Inf Zero

cSucc :: CTerm -> CTerm
cSucc k = Inf (Succ k)

cNatElim :: CTerm -> CTerm -> CTerm -> CTerm -> CTerm
cNatElim m mz ms k = Inf (NatElim m mz ms k)

cEq :: CTerm -> CTerm -> CTerm -> CTerm
cEq a x y = Inf (Eq a x y)

cRefl :: CTerm -> CTerm -> CTerm
cRefl a x = Inf (Refl a x)

cEqElim :: CTerm -> CTerm -> CTerm -> CTerm -> CTerm -> CTerm -> CTerm
cEqElim a m mr x y e = Inf (EqElim a m mr x y e)

cSuccS :: CTerm -> CTerm
cSuccS k = Inf (SuccS k)

data Name
  = Global String -- Global variables are represented by name thus type string
  | Local Int -- to convert a bound variable into a free one
  | Quote Int
  deriving (Show, Eq)

data Value -- Values can now also be VStar or VPi
  = VLam (Value -> Value)
  | VStar
  | VPi Value (Value -> Value)
  | VNeutral Neutral
  | VNat -- extensions for Nat
  | VZero
  | VSucc Value
  | VNil Value -- extensions for Vec
  | VCons Value Value Value Value
  | VVec Value Value
  | VRefl Value Value -- extensions for Eq
  | VEq Value Value Value
  -- extensions for size type
  | VSize -- size type
  | VInfty -- size limit
  | VSuccS Value -- size successor

-- size successor: s infty = infty
sinfty :: Value -> Value
sinfty VInfty = VInfty
sinfty v      = VSuccS v

showVal :: Value -> String
showVal (VLam _)         = "\\ "
showVal VStar            = "* "
showVal (VPi v _f)       = "pi " ++ showVal v ++ " -> lambda"
showVal (VNeutral _n)    = "neutral "
showVal VNat             = "Nat "
showVal VZero            = "Z "
showVal (VSucc v)        = "(S " ++ " " ++ showVal v ++ ")"
showVal (VNil t)         = "Vec " ++ showVal t ++ " 0"
showVal (VCons a k x xs) = "Cons " ++ concatMap showVal [a, k, x, xs]
showVal (VVec t l)       = "Vec " ++ showVal t ++ " Length " ++ showVal l
showVal (VRefl x y)      = "Refl " ++ showVal x ++ showVal y
showVal (VEq a x y)      = "Eq " ++ concatMap showVal [a, x, y]
showVal VSize            = "Size"
showVal VInfty           = "∞"
showVal (VSuccS s)       = "(Size S " ++ " " ++ showVal s ++ ")"

data Neutral
  --A neutral term is either a variable or an application of a neutral term to a value
  = NFree Name --vfree creates the value corresponding to a free variable
  | NApp Neutral Value
  | NNatElim Value Value Value Neutral -- for NatElim to not be stuck
  | NVecElim Value Value Value Value Value Neutral -- for VecElim
  | NEqElim Value Value Value Value Value Neutral -- for EqElim

vfree :: Name -> Value
vfree n = VNeutral (NFree n)

type Type = Value

type Context = [(Name, Type)] --Contexts map variables to their types.

type Env = [Value]

{-Quotation: takes a value back to a term-}
quote0 :: Value -> CTerm
quote0 = quote 0

quote :: Int -> Value -> CTerm
quote ii (VLam f) = Lam (quote (ii + 1) (f (vfree (Quote ii))))
quote ii (VNeutral n) = Inf (neutralQuote ii n)
quote _ii VStar = cStar
quote ii (VPi v f) = cPi (quote ii v) (quote (ii + 1) (f (vfree (Quote ii))))
  --for Nat
quote _ii VNat = cNat
quote _ii VZero = cZero
quote ii (VSucc n) = cSucc (quote ii n)
  --for Vec
quote ii (VVec a n) = Inf (Vec (quote ii a) (quote ii n))
quote ii (VNil a) = Inf (Nil (quote ii a))
quote ii (VCons a n x xs) =
  Inf (Cons (quote ii a) (quote ii n) (quote ii x) (quote ii xs))
  --for Eq
quote ii (VEq a x y) = cEq (quote ii a) (quote ii x) (quote ii y)
quote ii (VRefl x y) = cRefl (quote ii x) (quote ii y)
quote _ii VSize = Inf Size
quote _ii VInfty = Inf Infty
quote ii (VSuccS n) = cSuccS (quote ii n)

neutralQuote :: Int -> Neutral -> ITerm
neutralQuote ii (NFree x) = boundfree ii x
neutralQuote ii (NApp n v) = App (neutralQuote ii n) (quote ii v)
neutralQuote ii (NNatElim m z s n) =
  NatElim (quote ii m) (quote ii z) (quote ii s) (Inf (neutralQuote ii n))
neutralQuote ii (NVecElim a m mn mc n xs) =
  VecElim
    (quote ii a)
    (quote ii m)
    (quote ii mn)
    (quote ii mc)
    (quote ii n)
    (Inf (neutralQuote ii xs))
neutralQuote ii (NEqElim a m mr x y eq) =
  EqElim
    (quote ii a)
    (quote ii m)
    (quote ii mr)
    (quote ii x)
    (quote ii y)
    (Inf (neutralQuote ii eq))
  --checks if the variable occurring at the head of the application is a bound variable or a free name

boundfree :: Int -> Name -> ITerm
boundfree ii (Quote k) = Bound (ii - k - 1)
boundfree _ii x        = Free x
