module TypeChecker where

import           CheckDataDecl
import           CheckFunDecl
import           Control.Monad.State
import           Evaluator
import           Prelude
import           Types

-- 1. check expressions (see CheckExpr.hs)
-- 2. check functions (including clauses & patterns) (see CheckFunDecl.hs)
-- 3. check data declaration (including constructor and strict positivity.) (see
--    CheckDataDecl.hs)
-- 4. check declarations (including data declaration and function declaration)
--
typeCheckDeclaration :: Declaration -> TypeCheck ()
typeCheckDeclaration (DataDecl n sz pos tel t cs) = do
  sig <- get
  let dt = teleToType tel t
      params = length tel
      p' =
        case sz of
          Sized    -> params + 1
          NotSized -> params
  checkDataType 0 [] [] p' dt
  v <- eval [] dt
  put $ addSig sig n (DataSig params pos sz v)
  mapM_ (typeCheckConstructor n sz pos tel) cs
typeCheckDeclaration (FunDecl funs) = undefined
