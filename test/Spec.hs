import           CheckExpr
import           Control.Exception
import           Control.Monad.State.Lazy
import           Types

checkExprResult :: Either String () -> String
checkExprResult r =
  case r of
    Right _    -> "()"
    Left error -> error

main :: IO ()
main = do
  r <- evalStateT (checkExpr 0 [] [] Star VSize) emptySig
  putStrLn $ "`checkExpr 0 [] [] Star VStar` returns " <> checkExprResult r
