module TypeChecker where

import CheckDataType
    ( typeCheckConstructor, teleToType, checkDataType )
import CheckFunction ( typeCheckFuns )
import Control.Monad.State ( MonadState(put, get) )
import           Evaluator
import           Prelude
import           Types

typeCheckDeclaration :: Declaration -> TypeCheck ()
-- DataDecl Name Sized [Pos] Telescope Expr [TypeSig]
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
typeCheckDeclaration (FunDecl funs) = typeCheckFuns funs
