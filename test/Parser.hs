module Main where

import Test.Tasty
import Test.Tasty.Runners (TestTree (..))

main :: IO ()
main = defaultMain testParser

testParser :: TestTree
testParser =
  TestGroup
    "Parser tests"
    []
