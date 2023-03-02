module Main where

import Control.DeepSeq

import GHC.Conc (setNumCapabilities)

import System.Environment (getArgs)

import Conquer

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- mps 16 +RTS

main = do
  [benchmark, cores] <- getArgs
  let func = case benchmark of
        "mps" -> mpsBenchmark
        "mss" -> mssBenchmark
  setNumCapabilities (read cores)
  () <- return $ rnf func
  return ()
