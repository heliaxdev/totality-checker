module Pattern where

import           CheckExpr           (checkExpr)
import           Control.Monad.State (get)
import           Evaluator
import           SPos                (nonOccur)
import           Types

-- a substitution is a list of a partial mapping of generic values to values.
type Substitution = [(Int, Value)]

checkPatterns ::
     Int
  -> [(Int, (Expr, Value))]
  -> Substitution
  -> Env
  -> Env
  -> Value
  -> [Pattern]
  -> TypeCheck (Int, [(Int, (Expr, Value))], Substitution, Env, Env, Value)
checkPatterns k flex ins rho gamma v [] = return (k, flex, ins, rho, gamma, v)
checkPatterns k flex ins rho gamma v (p:pl) = do
  (k', flex', ins', rho', gamma', v') <- checkPattern k flex ins rho gamma v p
  checkPatterns k' flex' ins' rho' gamma' v' pl

-- checkPattern only checks for accessible patterns.
-- dot patterns will be represented by fresh flexible generic values,
-- which will be instantiated to concrete values when checking constructor patterns.
checkPattern ::
     Int -- next free generic value
  -> [(Int, (Expr, Value))] -- (flex variable, (its dot pattern, type))
  -> Substitution -- [(Int, Value)], (flex variable, its valuation)
  -> Env -- binding of variables to values
  -> Env -- binding of variables to their types
  -> Value -- type of the expression
  -> Pattern -- the pattern to check (variable/constructor/dot pattern)
  -- updated versions of the 6 inputs after a pattern is checked
  -> TypeCheck (Int, [(Int, (Expr, Value))], Substitution, Env, Env, Value)
checkPattern k flex ins rho gamma (VPi x av env b) (VarP y) = do
  let gk = VGen k -- variable patterns are converted to generic values
  bv <- eval (updateEnv env x gk) b
  return (k + 1, flex, ins, updateEnv rho y gk, updateEnv gamma y av, bv)
checkPattern k flex ins rho gamma (VPi x av env b) (ConP n pl) = do
  sig <- get
  let ConSig vc = lookupSig n sig
  (k', flex', ins', rho', gamma', vc') <-
    checkPatterns k flex ins rho gamma vc pl
  let flexgen = map fst flex'
  sub <- inst k' flexgen vc' av -- instantiate flex variables
  let pv = patternToVal k (ConP n pl)
  vb <- eval (updateEnv env x pv) b
  -- composition of substitutions from checkPatterns and instantiated flex var
  ins'' <- compSubst ins' sub
  vb' <- substVal ins'' vb -- substitute generic variable in value
  gamma'' <- substEnv ins'' gamma'
  return (k', flex', ins'', rho', gamma'', vb')
checkPattern k flex ins rho gamma (VPi x av env b) (DotP e) = do
  vb <- eval (updateEnv env x (VGen k)) b
  return (k + 1, (k, (e, av)) : flex, ins, rho, gamma, vb)
checkPattern _k _flex _ins _rho _gamma v _ = error $ "checkpattern: " <> show v

-- match v1 against v2 by unification, yielding a substition
inst :: Int -> [Int] -> Value -> Value -> TypeCheck Substitution
inst m flex v1 v2 =
  case (v1, v2) of
    (VGen k, _)
      | k `elem` flex -- if k is a dot pattern
       -> do
        noc <- nonOccur m v1 v2 -- check for non-occurence
        if noc -- if v1 is not in v2
          then return [(k, v2)] -- instantiate k to v2
          else error "inst: occurs check failed"
    (_, VGen k)
      | k `elem` flex -> do
        noc <- nonOccur m v2 v1
        if noc
          then return [(k, v1)]
          else error "inst: occurs check failed"
    (VApp (VDef d1) vl1, VApp (VDef d2) vl2)
      | d1 == d2 -> instList m flex vl1 vl2
    (VApp (VCon c1) vl1, VApp (VCon c2) vl2)
      | c1 == c2 -> instList m flex vl1 vl2
    (VSucc v1', VSucc v2') -> inst m flex v1' v2'
    (VSucc v, VInfty) -> inst m flex v VInfty
    _ -> do
      eqVal m v1 v2
      return []

instList :: Int -> [Int] -> [Value] -> [Value] -> TypeCheck Substitution
instList _m _flex [] [] = return []
instList m flex (v1:vl1) (v2:vl2) = do
  sub <- inst m flex v1 v2
  vl1' <- mapM (substVal sub) vl1
  vl2' <- mapM (substVal sub) vl2
  sub' <- instList m flex vl1' vl2'
  compSubst sub sub'
instList _ _ [] (_:_) =
  error "instList: the second input value list is longer than the first one. "
instList _ _ (_:_) [] =
  error "instList: the first input value list is longer than the second one. "

-- composition of substitutions:
-- given substitutions sub1 and sub2, using `sub1 sub2{v} = sub2 {sub1{v}}`
-- merge two substitutions into one such that
-- compSubst ((k1,v1)...(kn,vn)) sub2 = ((k1,sub2{v1})...(kn,sub2{vn}))
compSubst :: Substitution -> Substitution -> TypeCheck Substitution
compSubst sub1 sub2 = do
  let (dom1, tg1) = unzip sub1
  tg1' <- mapM (substVal sub2) tg1
  let sub1' = zip dom1 tg1'
  return $ sub1' <> sub2

-- substitute generic variable in value
substVal :: Substitution -> Value -> TypeCheck Value
substVal sub (VGen k) =
  case lookup k sub of
    Nothing -> return $ VGen k
    Just v' -> return v'
substVal sub (VApp v1 vl) = do
  v1' <- substVal sub v1
  vl' <- mapM (substVal sub) vl
  return $ VApp v1' vl'
substVal sub (VSucc v1) = do
  v1' <- substVal sub v1
  return $ sinfty v1'
substVal sub (VPi x av env b) = do
  av' <- substVal sub av
  env' <- substEnv sub env
  return $ VPi x av' env' b
substVal sub (VLam x env b) = do
  env' <- substEnv sub env
  return $ VLam x env' b
substVal _sub v = return v

-- substitute in environment
substEnv :: Substitution -> Env -> TypeCheck Env
substEnv _sub [] = return []
substEnv sub ((x, v):env) = do
  v' <- substVal sub v
  env' <- substEnv sub env
  return $ (x, v') : env'

-- convert a pattern to a value (for type checking later)
patternToVal :: Int -> Pattern -> Value
patternToVal k p = fst (p2v k p)

-- turn a pattern into (value, k)
p2v :: Int -> Pattern -> (Value, Int)
p2v k p =
  case p of
    VarP _p -> (VGen k, k + 1) -- var patterns are converted to flex k's.
    -- con patterns with an empty list of patterns are just Con.
    ConP n [] -> (VCon n, k)
    -- con patterns with pattern list pl are app of Con to the patterns.
    ConP n pl ->
      let (vl, k') = ps2vs k pl
       in (VApp (VCon n) vl, k')
    SuccP _p ->
      let (v, k') = p2v k p
       in (VSucc v, k')
    -- dot patterns are converted to flex k's.
    DotP _e -> (VGen k, k + 1)

-- turn a list of patterns to a list of values.
-- used in turning constructor patterns to values.
ps2vs :: Int -> [Pattern] -> ([Value], Int)
ps2vs k [] = ([], k)
ps2vs k (p:pl) =
  let (v, k') = p2v k p
      (vl, k'') = ps2vs k' pl
   in (v : vl, k'')

-- check inaccessible patterns. Check that
-- the expressions are equal to those instantiated in checkPattern
checkDot ::
     Int -> Env -> Env -> Substitution -> (Int, (Expr, Value)) -> TypeCheck ()
checkDot k rho gamma subst (i, (e, tv)) =
  case lookup i subst -- lookup the substitution of flex value i
        of
    Nothing ->
      error $
      "checkDot: cannot find the substitution for flex value (" <> show i <>
      ", (" <>
      show e <>
      ", " <>
      show tv <>
      ")). "
    Just v -> do
      tv' <- substVal subst tv
      checkExpr k rho gamma e tv'
      v' <- eval rho e
      eqVal k v v'
