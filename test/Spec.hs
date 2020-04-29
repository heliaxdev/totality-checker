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

testTargetErr :: Name -> Telescope -> Expr -> T.Test
testTargetErr name tel e =
  T.TestCase
    (TP.assertThrowsExact
       (ErrorCall "")
       (evalStateT (checkTarget name tel e) emptySig))

testDataType :: Int -> Env -> Env -> Int -> Expr -> T.Test
testDataType k rho gamma p e =
  T.TestCase
    (do result <- evalStateT (checkDataType k rho gamma p e) emptySig
        T.assertEqual
          ("checkDataType " <> show k <> show rho <> show gamma <> show p <>
           show e <>
           "should return ()")
          result
          ())

testDataTypeErr :: Int -> Env -> Env -> Int -> Expr -> T.Test
testDataTypeErr k rho gamma p e =
  T.TestCase
    (TP.assertThrowsExact
       (ErrorCall "")
       (evalStateT (checkDataType k rho gamma p e) emptySig))

testTargetList =
  T.TestList
    -- a definition matches its name
    [ T.TestLabel "testTargetDefn" (testTarget "n" [] (Def "n"))
    , T.TestLabel "testTargetApp" (testTarget "name" [] (App (Def "name") []))
    -- application of a var has a name that matches what's in the telescope
    , T.TestLabel
        "testTargetAppEl"
        (testTarget "name" [("var", Star)] (App (Def "name") [Var "var"]))
    -- names that don't match should raise an error
    , T.TestLabel
        "testTargetErrDef"
        (testTargetErr "na" [] (App (Def "name") []))
    , T.TestLabel
        "testTargetErrApp"
        (testTargetErr "name" [("var", Star)] (App (Def "name") [Var "notVar"]))
    ]

testDataTypeList =
  T.TestList
    [ T.TestLabel "testDataTypeStar" (testDataType 0 [] [] 0 Star)
    , T.TestLabel "testDataTypeConErr" (testDataTypeErr 0 [] [] 0 (Con "con"))
    ]

main = do
  putStrLn ""
  putStrLn "checkTarget tests:"
  T.runTestTT testTargetList
  putStrLn "checkDataType tests:"
  T.runTestTT testDataTypeList
  return ()
