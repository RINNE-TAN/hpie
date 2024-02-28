module Main where

import Hpie.TopLevel (topLevelMain)

main :: IO ()
main = do
  input <- readFile "W.txt"
  mapM_ print $ topLevelMain input
