{-# LANGUAGE TemplateHaskell, FlexibleContexts, ViewPatterns, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Criterion.Main
import Criterion.Types

import GHC.Conc (setNumCapabilities)

import System.IO.Unsafe

import Conquer

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- +RTS -N16

runWith :: a -> Int -> a
runWith p num = seq (unsafePerformIO (setNumCapabilities num)) p

main = do
  defaultMain [ bgroup "mps"[ bench "1 core" $ nf (runWith mpsTest) 1
                            , bench "2 cores" $ nf (runWith mpsTest) 2
                            , bench "4 cores" $ nf (runWith mpsTest) 4
                            , bench "6 cores" $ nf (runWith mpsTest) 6
                            , bench "8 cores" $ nf (runWith mpsTest) 8
                            {-, bench "10 cores" $ nf (runWith mpsTest) 10
                            , bench "12 cores" $ nf (runWith mpsTest) 12
                            , bench "14 cores" $ nf (runWith mpsTest) 14
                            , bench "16 cores" $ nf (runWith mpsTest) 16
                            , bench "18 cores" $ nf (runWith mpsTest) 18
                            , bench "20 cores" $ nf (runWith mpsTest) 20-}
                            ]
              ]
