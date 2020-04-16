module Pattern where

import           Types

patternToVal :: Int -> Pattern -> Value
patternToVal k p = fst (p2v k p)

-- turn a pattern into (value, k)
-- dot patterns get variables corresponding to their flexible generic value
p2v :: Int -> Pattern -> (Value, Int)
p2v k p =
  case p of
    VarP _p -> (VGen k, k + 1)
    ConP n [] -> (VCon n, k)
    ConP n pl ->
      let (vl, k') = ps2vs k pl
       in (VApp (VCon n) vl, k')
    SuccP _p ->
      let (v, k') = p2v k p
       in (VSucc v, k')
    DotP _e -> (VGen k, k + 1)

ps2vs :: Int -> [Pattern] -> ([Value], Int)
ps2vs k [] = ([], k)
ps2vs k (p:pl) =
  let (v, k') = p2v k p
      (vl, k'') = ps2vs k' pl
   in (v : vl, k'')
