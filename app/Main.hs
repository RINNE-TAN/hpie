module Main where

import Hpie.Parser

main :: IO ()
main = do
  print res
  where
    res = runParser pProg ""