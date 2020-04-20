module SPos where

import           Control.Monad.State
import           Evaluator
import           Types

-- to check data type declarations, one has to check
-- strict positivity of the constructors.
--
-- check that recursive data argument n and
-- the spos declared parameter variables are only used strictly positively
sposConstructor :: Name -> Int -> [Pos] -> Value -> TypeCheck ()
sposConstructor n k sp (VPi x av env b) = do
  spr <- spos 0 (VDef n) av
  spv <- sposVals (posGen 0 sp) av
  case (spr, spv) of
    (True, True) -> do
      bv <- eval (updateEnv env x (VGen k)) b
      sposConstructor n (k + 1) sp bv
    (False, _) -> error "rec. arg not strictly positive"
    (True, False) -> error "parameter not strictly positive"
sposConstructor _n _k _sp _ = return ()

sposVals :: [Value] -> Value -> TypeCheck Bool
sposVals vals tv = do
  sl <- mapM (\i -> spos 0 i tv) vals
  return $ and sl

posGen :: Int -> [Pos] -> [Value]
posGen _i [] = []
posGen i (p:pl) =
  case p of
    SPos  -> VGen i : posGen (i + 1) pl
    NSPos -> posGen (i + 1) pl

posArgs :: [Value] -> [Pos] -> ([Value], [Value])
posArgs vl pl =
  let l = zip vl pl
      l1 = [v | (v, SPos) <- l]
      l2 = [v | (v, NSPos) <- l]
   in (l1, l2)

-- check that a does occurs strictly pos tv
-- a may be a "atomic value" ie not pi, lam, app, or succ
spos :: Int -> Value -> Value -> TypeCheck Bool
spos k a (VPi x av env b) = do
  no <- nocc k a av
  if no
    then do
      bv <- eval (updateEnv env x (VGen k)) b
      spos (k + 1) a bv
    else return False
spos k a (VLam x env b) = do
  bv <- eval (updateEnv env x (VGen k)) b
  spos (k + 1) a bv
spos k a (VSucc v) = spos k a v
spos k a (VApp (VDef m) vl) = do
  sig <- get
  case lookupSig m sig of
    (DataSig p pos _ _) -> do
      let (pparams, nparams) = posArgs vl pos
      let rest = drop p vl
      sl <- mapM (spos k a) pparams
      nl <- mapM (nocc k a) (nparams <> rest)
      return $ and sl && and nl
    _ -> do
      nl <- mapM (nocc k a) vl
      return $ and nl
spos k a (VApp v' vl) =
  if v' == a
    then do
      nl <- mapM (nocc k a) vl
      return $ and nl
    else do
      n <- nocc k a v'
      nl <- mapM (nocc k a) vl
      return $ n && and nl
spos _k _a _ = return True
