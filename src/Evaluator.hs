module Evaluator where

import           Types

iEval :: ITerm -> Env -> Value -- Evaluation
iEval (Ann e _) d = cEval e d
iEval (Free x) _d = vfree x
iEval (Bound ii) d = d !! ii --(!!) :: [a] -> Int -> a. It's the list lookup operator.
iEval (App e1 e2) d = vapp (iEval e1 d) (cEval e2 d)
iEval Star _d = VStar
iEval (Pi ty ty') d = VPi (cEval ty d) (\x -> cEval ty' (x : d))
  --evaluation of Nat
iEval Nat _d = VNat
iEval Zero _d = VZero
iEval (Succ k) d = VSucc (cEval k d)
iEval (NatElim m mz ms k) d =
  let mzVal = cEval mz d
      msVal = cEval ms d
      rec kVal =
        case kVal of
          VZero -> mzVal
          VSucc l -> msVal `vapp` l `vapp` rec l
          VNeutral n -> VNeutral (NNatElim (cEval m d) mzVal msVal n)
          term ->
            error
              ("internal: eval natElim. \n" ++
               showVal term ++ "\n cannot be evaluated.")
   in rec (cEval k d)
  --evaluation of Vec
iEval (Nil a) d = VNil (cEval a d)
iEval (Cons a k x xs) d = VCons (cEval a d) (cEval k d) (cEval x d) (cEval xs d)
iEval (Vec a k) d = VVec (cEval a d) (cEval k d)
iEval (VecElim a m mn mc k xs) d =
  let mnVal = cEval mn d
      mcVal = cEval mc d
      rec kVal xsVal =
        case xsVal of
          VNil _ -> mnVal
          VCons _ l x xs_ -> foldl vapp mcVal [l, x, xs_, rec l xs_]
          VNeutral n ->
            VNeutral (NVecElim (cEval a d) (cEval m d) mnVal mcVal kVal n)
          term ->
            error
              ("internal: eval vecElim. \n" ++
               showVal term ++ " \n cannot be evaluated.")
   in rec (cEval k d) (cEval xs d)
  --evaluation of Eq
iEval (Refl x y) d = VRefl (cEval x d) (cEval y d)
iEval (Eq a x y) d = VEq (cEval a d) (cEval x d) (cEval y d)
iEval (EqElim a m mr x y eq) d =
  let mrVal = cEval mr d
      recu eqVal =
        case eqVal of
          VRefl _ z -> mrVal `vapp` z
          VNeutral n ->
            VNeutral
              (NEqElim (cEval a d) (cEval m d) mrVal (cEval x d) (cEval y d) n)
          term ->
            error
              ("internal: eval eqElim. \n " ++
               showVal term ++ "\n cannot be evaluated.")
   in recu (cEval eq d)
  -- evaluation of size type
iEval Size _d = VSize -- size type
iEval (SuccS s) d =
  let vs = cEval s d
   in sinfty vs -- size successor
iEval Infty _d = VInfty -- size infinity (limit size)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)
vapp x y =
  error
    ("Application (vapp) error. Cannot apply \n" ++
     showVal y ++ "\n to \n" ++ showVal x)

cEval :: CTerm -> Env -> Value
cEval (Inf ii) d = iEval ii d
cEval (Lam e) d  = VLam (\x -> cEval e (x : d))

{- Substitution:
substitution function for inferable terms-}
iSubst :: Int -> ITerm -> ITerm -> ITerm
iSubst ii r (Ann e ty) = Ann (cSubst ii r e) (cSubst ii r ty)
iSubst ii r (Bound j) =
  if ii == j
    then r
    else Bound j
iSubst _ii _r (Free y) = Free y
iSubst ii r (App e1 e2) = App (iSubst ii r e1) (cSubst ii r e2)
iSubst _ii _r Star = Star
iSubst ii r (Pi ty ty') = Pi (cSubst ii r ty) (cSubst (ii + 1) r ty')
  --for Nat
iSubst _ii _r Nat = Nat
iSubst _ii _r Zero = Zero
iSubst ii r (Succ n) = Succ (cSubst ii r n)
iSubst ii r (NatElim m mz ms n) =
  NatElim (cSubst ii r m) (cSubst ii r mz) (cSubst ii r ms) (cSubst ii r n)
  --for Vec
iSubst ii r (Vec a n) = Vec (cSubst ii r a) (cSubst ii r n)
iSubst ii r (Nil a) = Nil (cSubst ii r a)
iSubst ii r (Cons a n x xs) =
  Cons (cSubst ii r a) (cSubst ii r n) (cSubst ii r x) (cSubst ii r xs)
iSubst ii r (VecElim a m mn mc n xs) =
  VecElim
    (cSubst ii r a)
    (cSubst ii r m)
    (cSubst ii r mn)
    (cSubst ii r mc)
    (cSubst ii r n)
    (cSubst ii r xs)
  --for Eq
iSubst ii r (Eq a x y) = Eq (cSubst ii r a) (cSubst ii r x) (cSubst ii r y)
iSubst ii r (Refl x y) = Refl (cSubst ii r x) (cSubst ii r y)
iSubst ii r (EqElim a m mr x y eq) =
  EqElim
    (cSubst ii r a)
    (cSubst ii r m)
    (cSubst ii r mr)
    (cSubst ii r x)
    (cSubst ii r y)
    (cSubst ii r eq)
iSubst _ii _r Size = Size
iSubst _ii _r (SuccS n) = SuccS n
iSubst _ii _r Infty = Infty

{-substitution function for checkable terms-}
cSubst :: Int -> ITerm -> CTerm -> CTerm
cSubst ii r (Inf e) = Inf (iSubst ii r e)
cSubst ii r (Lam e) = Lam (cSubst (ii + 1) r e)
