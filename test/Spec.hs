import           CheckExpr
import           Control.Exception
import           Control.Monad.State.Lazy
import qualified Test.HUnit               as T
import           Types

testType :: Expr -> T.Test
testType e =
  T.TestCase
    (do r <- evalStateT (checkType0 e) emptySig
        T.assertEqual
          ("checkType0 " <> show e <> "should return Right ()")
          r
          (Right ()))

testlist = T.TestList [T.TestLabel "testTypeStar" (testType Star)]

main = do
  T.runTestTT testlist
  return ()
