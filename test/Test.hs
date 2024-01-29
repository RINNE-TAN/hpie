module Main where

import Hpie.Parser
import Hpie.Types
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Runners (TestTree (..))

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = TestGroup "Hpie tests" [testHello, testParser]

testHello :: TestTree
testHello = testCase "hello case" ("hello" @?= "hello")

testParser :: TestTree
testParser = TestGroup "Parser tests" [testVar]

testVar :: TestTree
testVar =
  testWithInput
    "Parser Var"
    [ ("a", Var "a"),
      ("a01", Var "a01"),
      ("xyz_1", Var "xyz_1")
    ]

testWithInput :: String -> [(String, Term)] -> TestTree
testWithInput groupName cases = TestGroup groupName (f <$> cases)
  where
    f (input, expect) = testCase ("input is :" ++ input) (checkParser input expect)

checkParser :: String -> Term -> Assertion
checkParser input expect =
  case runParser pTerm input of
    Left msg -> assertFailure (show msg)
    Right (i, term) -> (i @?= "") >> (term @?= expect)