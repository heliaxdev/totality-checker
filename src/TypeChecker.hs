-- Sized typed built on top of LambdaPi
module TypeChecker where

import           Prelude
import           Types

errorMsg :: Int -> Expr -> Value -> Value -> String
errorMsg binder e expectedT gotT =
  "Type mismatched. \n" <> show e <> " \n (binder number " <> show binder <>
  ") is of type \n" <>
  show gotT <>
  "\n but the expected type is " <>
  show expectedT <>
  "."
