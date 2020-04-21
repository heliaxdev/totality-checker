module CheckDataDecl where

import           Types

-- import SPos
typeCheckConstructor ::
     Name -> Sized -> [Pos] -> Telescope -> TypeSig -> TypeCheck ()
typeCheckConstructor name sz pos tel (TypeSig n t) = undefined

teleToType :: Telescope -> Expr -> Expr
teleToType [] t            = t
teleToType ((n, t):tel) t2 = Pi n t (teleToType tel t2)

typeToTele :: Expr -> (Telescope, Expr)
typeToTele t = ttt t []
  where
    ttt :: Expr -> Telescope -> (Telescope, Expr)
    ttt (Pi n t' t2) tel = ttt t2 (tel <> [(n, t')])
    ttt x tel            = (tel, x)
