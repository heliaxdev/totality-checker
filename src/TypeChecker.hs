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
typeCheckDeclaration (DataDecl n sz co pos tel t cs) = undefined
typeCheckDeclaration (FunDecl co funs)               = undefined
