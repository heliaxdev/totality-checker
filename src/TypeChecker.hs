-- Sized typed built on top of LambdaPi
module TypeChecker where

import           Control.Monad.Except

import           Evaluator            (cEval, cSubst, vapp)
import           Prelude
import           Types

type Result a = Either String a --when type checking fails, it throws an error.
  --inferable terms has type as output.

iType0 :: Context -> ITerm -> Result Type
iType0 = iType 0

iType :: Int -> Context -> ITerm -> Result Type
iType ii g (Ann e rho) = do
  cType ii g rho VStar
  let ty = cEval rho []
  cType ii g e ty
  return ty
iType _ii _g Star = return VStar
iType ii g (Pi rho rho') = do
  cType ii g rho VStar
  let ty = cEval rho []
  cType (ii + 1) ((Local ii, ty) : g) (cSubst 0 (Free (Local ii)) rho') VStar
  return VStar
iType ii g (Free x) =
  case lookup x g of
    Just ty -> return ty
    Nothing ->
      throwError
        ("Cannot find the type of \n" ++
         show x ++ "\n (binder number " ++ show ii ++ ") in the environment.")
iType ii g (App e1 e2) = do
  si <- iType ii g e1
  case si of
    VPi ty ty' -> do
      cType ii g e2 ty
      return (ty' (cEval e2 []))
    _ ->
      throwError
        (show e1 ++
         "\n (binder number " ++
         show ii ++
         ") is not a function type and thus \n" ++
         show e1 ++ "\n cannot be applied to it.")
  --type checker for Nat
iType _ii _g Nat = return VStar
iType _ii _g Zero = return VNat
iType ii g (Succ k) = do
  cType ii g k VNat
  return VNat
iType ii g (NatElim m mz ms k) = do
  cType ii g m (VPi VNat (const VStar))
  let mVal = cEval m []
  cType ii g mz (mVal `vapp` VZero)
  cType
    ii
    g
    ms
    (VPi VNat (\l -> VPi (mVal `vapp` l) (\_ -> mVal `vapp` VSucc l)))
  cType ii g k VNat
  let kVal = cEval k []
  return (mVal `vapp` kVal)
  --type checker for Vec
iType ii g (Vec a k) = do
  cType ii g a VStar
  cType ii g k VNat
  return VStar
iType ii g (Nil a) = do
  cType ii g a VStar
  let aVal = cEval a []
  return (VVec aVal VZero)
iType ii g (Cons a k x xs) = do
  cType ii g a VStar
  let aVal = cEval a []
  cType ii g k VNat
  let kVal = cEval k []
  cType ii g x aVal
  cType ii g xs (VVec aVal kVal)
  return (VVec aVal (VSucc kVal))
iType ii g (VecElim a m mn mc k vs) = do
  cType ii g a VStar
  let aVal = cEval a []
  cType ii g m (VPi VNat (\k_ -> VPi (VVec aVal k_) (const VStar)))
  let mVal = cEval m []
  cType ii g mn (foldl vapp mVal [VZero, VNil aVal])
  cType
    ii
    g
    mc
    (VPi
       VNat
       (\l ->
          VPi
            aVal
            (\y ->
               VPi
                 (VVec aVal l)
                 (\ys ->
                    VPi
                      (foldl vapp mVal [l, ys])
                      (\_ -> foldl vapp mVal [VSucc l, VCons aVal l y ys])))))
  cType ii g k VNat
  let kVal = cEval k []
  cType ii g vs (VVec aVal kVal)
  let vsVal = cEval vs []
  return (foldl vapp mVal [kVal, vsVal])
  --type checker for Eq
iType ii g (Eq a x y) = do
  cType ii g a VStar
  let aVal = cEval a []
  cType ii g x aVal
  cType ii g y aVal
  return VStar
iType ii g (Refl x y) = do
  let xVal = cEval x []
      yVal = cEval y []
  cType ii g x VStar
  cType ii g y xVal
  return (VEq xVal yVal yVal)
iType ii g (EqElim a m mr x y eq) = do
  cType ii g a VStar
  let aVal = cEval a []
  cType
    ii
    g
    m
    (VPi aVal (\x_ -> VPi aVal (\y_ -> VPi (VEq aVal x_ y_) (const VStar))))
  let mVal = cEval m []
  cType ii g mr (VPi aVal (\x_ -> foldl vapp mVal [x_, x_]))
  cType ii g x aVal
  let xVal = cEval x []
  cType ii g y aVal
  let yVal = cEval y []
  cType ii g eq (VEq aVal xVal yVal)
  return (foldl vapp mVal [xVal, yVal])
iType ii _g iterm =
  throwError
    (show iterm ++
     "\n (binder number " ++ show ii ++ ") is not an inferable term.")
  --error message for inferring/checking types

errorMsg :: Int -> ITerm -> Value -> Value -> String
errorMsg binder iterm expectedT gotT =
  "Type mismatched. \n" ++
  show iterm ++
  " \n (binder number " ++
  show binder ++
  ") is of type \n" ++
  show (showVal gotT) ++
  "\n but the expected type is " ++ show (showVal expectedT) ++ "."
  --checker for checkable terms checks the term against a type and returns ().

cType :: Int -> Context -> CTerm -> Type -> Result ()
cType ii g (Inf e) v = do
  v' <- iType ii g e
  unless (quote0 v == quote0 v') (throwError (errorMsg ii e v v'))
cType ii g (Lam e) (VPi ty ty') =
  cType
    (ii + 1)
    ((Local ii, ty) : g)
    (cSubst 0 (Free (Local ii)) e)
    (ty' (vfree (Local ii)))
cType ii _g cterm theType =
  throwError
    ("Type mismatch: \n" ++
     show cterm ++
     "\n (binder number " ++
     show ii ++
     ") is not a checkable term. Cannot check that it is of type " ++
     showVal theType)
  --motive for plusK

motivePlus :: CTerm
motivePlus = Lam (cPi cNat cNat)
  --following paper, plus add two Nats. plus :: Nat -> Nat -> Nat.

plus :: CTerm -> ITerm
plus =
  NatElim
    motivePlus -- motive
    (Lam (cBound 0)) --(\n -> n)
    --(\k \rec \n -> Succ(rec n)), where rec is adding k
    (Lam (Lam (Lam (cSucc (Inf (App (Bound 1) (cBound 0)))))))
  --plusZero adds zero to a Nat. plusZero :: Nat -> Nat.

plusZero :: ITerm
plusZero = plus cZero

plusOne :: ITerm
plusOne = plus (cSucc cZero)

plusTwo :: ITerm
plusTwo = plus (cSucc (cSucc cZero))

plusZeroIsIdentityIMType :: CTerm
plusZeroIsIdentityIMType =
  cPi cNat (cPi cNat (cPi (cEq cNat (cBound 1) (cBound 2)) cStar))
  --Proof of x + 0 = x
  --Turn plusZeroIsIdentityIM from a CTerm to an ITerm.

iplusZeroIsIdentityIM :: ITerm
iplusZeroIsIdentityIM = Ann plusZeroIsIdentityIMType plusZeroIsIdentityIM
  --the motive of the EqElim for plusZeroIsIdentityInductive

plusZeroIsIdentityIM :: CTerm
plusZeroIsIdentityIM =
  Lam --x::Nat, in this case plus x 0
    (Lam --y::Nat, in this case x
       (Lam --of type Eq a x y
          --output has to be of type type,
          --in this case Eq Nat (plus (Succ x) 0) (Succ x)
          (cEq cNat (Inf (App plusZero (cSucc (cBound 1)))) (cSucc (cBound 1)))))
  --The function to prove inductive case of plusZeroIsIdentity.
  --plusZeroIsIdentityInductive ::
  --For all k::Nat.Eq Nat (plusZero k) k -> Eq Nat (plusZero (Succ k)) (Succ k)

plusZeroIsIdentityInductive :: CTerm
plusZeroIsIdentityInductive =
  Lam --k :: Nat
    (Lam
       (cEqElim
          --1st argument: of type type, in this case Nat.
          (cBound 0)
          --2nd argument: motive, takes in x, y, Eq a x y and returns a type,
          --in this case it's Eq Nat (plusZero (Succ k)) (Succ k)
          plusZeroIsIdentityIM
          --3rd argument, resulting type should be Eq Nat (plusZero (Succ k)) (Succ k).
          (Lam (cRefl cNat (cSucc (cBound 0))))
          --4th argument, x, of type Nat
          (Inf (App plusZero (cBound 1)))
          --5th argument, y, of type Nat
          (cBound 1)
          --6th argument, of type Eq a x y
          (cRefl cNat (cBound 1))))

plusZeroIsIdentity :: CTerm -> ITerm
plusZeroIsIdentity =
  NatElim --point-free style, x is omitted
    --motive takes in x and returns the type Eq Nat (x+0) x, \x. Eq Nat (x + 0) x
    (Lam (cEq cNat (Inf (App plusZero (cBound 0))) (cBound 0)))
    (cRefl cNat cZero) --m Zero, with type Eq Nat 0 0.
    --inductive case, the result have to be of type Eq Nat (k + 1 + 0) (k + 1)
    plusZeroIsIdentityInductive
  --Proof of x + y = y + x
  --the motive of the EqElim for plusCommInductive

plusCommIM :: CTerm
plusCommIM =
  Lam
    (Lam
       (Lam
          (cEq
             cNat
             (Inf (App (plus (cSucc (cBound 2))) (cBound 1)))
             (Inf (App (plus (cBound 1)) (cSucc (cBound 2)))))))
  --The function to prove inductive case of plusComm.
  --plusComm :: For all k,x::Nat, Eq Nat (plus k x) (plus x k) -> Eq Nat (plus (Succ k) x) (plus x (Succ k))

plusCommInductive :: CTerm
plusCommInductive =
  Lam --k::Nat
    (Lam --x::Nat
       (Lam
          (cEqElim
        --first argument of EqElim, of type type, in this case Nat
             (cBound 0)
            --2nd argument: motive, takes in x, y, Eq a x y and returns a type,
            --in this case it's Eq Nat (plus (Succ k) x) (plus x (Succ k))
             plusCommIM
            --3rd argument, resulting type should be Eq Nat (plus (Succ k) x) (plus x (Succ k)).
             (Lam (cRefl cNat (cSucc (cBound 2))))
            --4th argument, x, of type Nat
             (Inf (App (plus (cBound 2)) (cBound 1)))
            --5th argument, y, of type Nat
             (Inf (App (plus (cBound 1)) (cBound 2)))
            --6th argument, of type Eq a x y
             (cRefl cNat (Inf (App (plus (cBound 1)) (cBound 2)))))))

plusComm :: CTerm -> CTerm -> ITerm
plusComm _x =
  NatElim
    --motive takes in x and y and returns the type Eq Nat (plus x y) (plus y x)
    (Lam
       (Lam
          (cEq
             cNat
             (Inf (App (plus (cBound 1)) (cBound 0)))
             (Inf (App (plus (cBound 0)) (cBound 1))))))
    (cRefl cNat (Inf (App plusZero (cBound 1)))) --m Zero, x + 0 = 0 + x
    --inductive case, the result have to be of type Eq Nat (x + (k+1)) ((k+1) + x)
    plusCommInductive
