import           CheckDataType
import           CheckExpr
import           Control.Exception
import           Control.Monad.State.Lazy
import qualified Test.HUnit               as T
import           Test.HUnitPlus.Base      as TP
import           Types

testTarget :: Name -> Telescope -> Expr -> T.Test
testTarget name tel e =
  T.TestCase
    (do result <- evalStateT (checkTarget name tel e) emptySig
        T.assertEqual
          ("checkTarget " <> show name <> show tel <> show e <>
           " should return ()")
          result
          ())

testTargetFail :: Name -> Telescope -> Expr -> T.Test
testTargetFail name tel e =
  T.TestCase
    (TP.assertThrowsExact
       (ErrorCall "anything")
       (evalStateT (checkTarget name tel e) emptySig))

testType :: Expr -> T.Test
testType e =
  T.TestCase
    (do result <- evalStateT (checkType0 e) emptySig
        T.assertEqual
          ("checkType0 " <> show e <> " should return Right ()")
          result
          (Right ()))

testTargetList =
  T.TestList
    [ T.TestLabel "testTypeStar" (testType Star)
    -- a definition matches its name
    , T.TestLabel "testTargetDefn" (testTarget "n" [] (Def "n"))
    , T.TestLabel "testTargetApp" (testTarget "name" [] (App (Def "name") []))
    -- application of a var has a name that matches what's in the telescope
    , T.TestLabel
        "testTargetAppEl"
        (testTarget "name" [("var", Star)] (App (Def "name") [Var "var"]))
    -- names that don't match should raise an error
    , T.TestLabel
        "testTargetFailDef"
        (testTargetFail "na" [] (App (Def "name") []))
    , T.TestLabel
        "testTargetFailApp"
        (testTargetFail "name" [("var", Star)] (App (Def "name") [Var "notVar"]))
    ]

testlist = testTargetList

main = do
  T.runTestTT testlist
  return ()
