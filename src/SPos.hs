module SPos where

import           Types

data Pos -- positivity
  = SPos
  | NSPos
  deriving (Eq, Show)
-- -- check that recursive data argument n and the spos declared parameter variables are only used strictly positvly
-- sposConstructor :: Name -> Int -> [Pos] -> Value -> TypeCheck ()
-- sposConstructor n k sp tv =
--   case tv of
--     VPi x av env b -> do
--       spr <- spos 0 (VDef n) av
--       spv <- sposVals (posGen 0 sp) av
--       case (spr, spv) of
--         (True, True) -> do
--           bv <- whnf (update env x (VGen k)) b
--           sposConstructor n (k + 1) sp bv
--         (False, _) -> throwErrorMsg "rec. arg not strictly positive"
--         (True, False) -> throwErrorMsg "parameter not strictly positive"
--     _ -> return ()
-- sposVals :: [Value] -> Value -> TypeCheck Bool
-- sposVals vals tv = do
--   sl <- mapM (\i -> spos 0 i tv) vals
--   return $ and sl
-- posGen :: Int -> [Pos] -> [Value]
-- posGen i [] = []
-- posGen i (p:pl) =
--   case p of
--     SPos  -> VGen i : posGen (i + 1) pl
--     NSPos -> posGen (i + 1) pl
-- posArgs :: [Value] -> [Pos] -> ([Value], [Value])
-- posArgs vl pl =
--   let l = zip vl pl
--       l1 = [v | (v, SPos) <- l]
--       l2 = [v | (v, NSPos) <- l]
--    in (l1, l2)
-- -- check that a does occurs strictly pos tv
-- -- a may be a "atomic value" ie not pi , lam , app , or succ
-- spos :: Int -> Value -> Value -> TypeCheck Bool
-- spos k a tv -- trace ("noccRecArg " ++ show tv)
--  =
--   case tv of
--     VPi x av env b -> do
--       no <- nocc k a av
--       if no
--         then do
--           bv <- whnf (update env x (VGen k)) b
--           spos (k + 1) a bv
--         else return False
--     VLam x env b -> do
--       bv <- whnf (update env x (VGen k)) b
--       spos (k + 1) a bv
--     VSucc v -> spos k a v
--     VApp v' vl
--       | v' == a -> do
--         nl <- mapM (nocc k a) vl
--         return $ and nl
--     VApp (VDef m) vl -> do
--       sig <- get
--       case lookupSig m sig of
--         (DataSig p pos _ _ _) -> do
--           let (pparams, nparams) = posArgs vl pos
--           let rest = drop p vl
--           sl <- mapM (spos k a) pparams
--           nl <- mapM (nocc k a) (nparams ++ rest)
--           return $ and sl && and nl
--         _ -> do
--           nl <- mapM (nocc k a) vl
--           return $ and nl
--     VApp v1 vl -> do
--       n <- nocc k a v1
--       nl <- mapM (nocc k a) vl
--       return $ n && and nl
--     _ -> return True
