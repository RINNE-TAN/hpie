module Main where

import Hpie.Parser
import Hpie.Types
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Runners (TestTree (..))

main :: IO ()
main = defaultMain testParser

testParser :: TestTree
testParser =
  TestGroup
    "Parser tests"
    [ testVar,
      testVarError,
      testPi,
      testApp
    ]

testWithInput :: String -> (String -> a -> Assertion) -> [(String, a)] -> TestTree
testWithInput groupName asssertF cases = TestGroup groupName (f <$> cases)
  where
    f (input, expect) = testCase ("input is :" ++ input) (asssertF input expect)

parserSucc :: String -> Term -> Assertion
parserSucc input expect =
  case runParser (pTerm <* spaces) input of
    Left msg -> assertFailure (show msg)
    Right (i, term) -> (i @?= "") >> (term @?= expect)

parserError :: String -> ParserError -> Assertion
parserError input expectError =
  case runParser (pTerm <* spaces) input of
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
      (" (aa )", Var "aa")
    ]

testVarError :: TestTree
testVarError =
  testWithInput
    "Parser Var"
    parserError
    [ ("_1dada", Unexpected "_1dada"),
      ("1aa02", Unexpected "1aa02"),
      ("", EOF)
    ]

testPi :: TestTree
testPi =
  testWithInput
    "Parser Pi"
    parserSucc
    [("Π(x: b) a", Pi "x" (Var "b") (Var "a"))]

testApp :: TestTree
testApp =
  testWithInput
    "Parser App"
    parserSucc
    [ ("(a b)", App (Var "a") (Var "b")),
      ( "(Π(x: Nat) a) b",
        App
          (Pi "x" Nat (Var "a"))
          (Var "b")
      ),
      ( "(λ (x) y) z",
        App
          (Lam "x" (Var "y"))
          (Var "z")
      )
    ]