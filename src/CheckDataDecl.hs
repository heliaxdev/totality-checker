module CheckDataDecl where

import           Types

-- import SPos
typeCheckConstructor ::
     Name -> Sized -> [Pos] -> Telescope -> Constructor -> TypeCheck ()
typeCheckConstructor name sz pos tel (TypeSig n t) = undefined

teleToType :: Telescope -> Type -> Type
teleToType [] t            = t
teleToType ((n, t):tel) t2 = Pi n t (teleToType tel t2)

typeToTele :: Type -> (Telescope, Type)
typeToTele t = ttt t []
  where
    ttt :: Type -> Telescope -> (Telescope, Type)
    ttt (Pi n t' t2) tel = ttt t2 (tel <> [(n, t')])
    ttt x tel            = (tel, x)
