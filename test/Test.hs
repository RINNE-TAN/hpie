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
testParser = TestGroup "Parser tests" [testVar, testVarError, testPi]

testWithInput :: String -> (String -> a -> Assertion) -> [(String, a)] -> TestTree
testWithInput groupName asssertF cases = TestGroup groupName (f <$> cases)
  where
    f (input, expect) = testCase ("input is :" ++ input) (asssertF input expect)

parserSucc :: String -> Term -> Assertion
parserSucc input expect =
  case runParser pProg input of
    Left msg -> assertFailure (show msg)
    Right (i, term) -> (i @?= "") >> (term @?= expect)

parserError :: String -> ParserError -> Assertion
parserError input expectError =
  case runParser pProg input of
    Left e -> e @?= expectError
    Right (_, term) -> assertFailure ("expect error but get:" ++ show term)

testVar :: TestTree
testVar =
  testWithInput
    "Parser Var"
    parserSucc
    [ ("a", Var "a"),
      ("a01", Var "a01"),
      ("xADz_1", Var "xADz_1"),
      (" aa ", Var "aa"),
      (" (aa)", Var "aa")
    ]

testVarError :: TestTree
testVarError =
  testWithInput
    "Parser Var"
    parserError
    [ ("_1dada", Unexpected),
      ("1aa02", Unexpected),
      ("", EOF)
    ]

testPi :: TestTree
testPi =
  testWithInput
    "Parser Pi"
    parserSucc
    [("Π(x:b) a", Pi "x" (Var "b") (Var "a"))]