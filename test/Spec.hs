import           CheckExpr
import           Control.Exception
import           Control.Monad.State.Lazy
import qualified Test.HUnit               as T
import           Types

testTypeStar :: T.Test
testTypeStar =
  T.TestCase
    (do r <- evalStateT (checkType 0 [] [] Star) emptySig
        T.assertEqual "should return" r (Right ()))

testlist = T.TestList [T.TestLabel "testTypeStar" testTypeStar]

main = do
  T.runTestTT testlist
  return ()
