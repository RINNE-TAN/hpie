module Main where

import Hpie.TopLevel (topLevelMain)

main :: IO ()
main = do
  input <- readFile "example/pair.pi"
  msg <- topLevelMain input
  case msg of
    Left e -> print e
    _ -> return ()
