-- {-# OPTIONS_GHC -fno-full-laziness #-}
{-# LANGUAGE OverloadedStrings     #-}

module Main where

import Control.DeepSeq
import Control.Exception

import Formatting
import Formatting.Clock


--import GHC.Conc     (setNumCapabilities)

import System.Clock
import System.Environment

import Conquer
import Z

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- +RTS -N16

{-main2 = do
  args <- getArgs
  setNumCapabilities (read (head args))
  () <- return (rnf (mpsTest ()))
  return ()

main3 num = do
  setNumCapabilities num
  () <- return (rnf (mpsTest ()))
  return ()-}

bench () = do
  start <- getTime ProcessCPUTime
  () <- return $ rnf $ mpsTest (take 2000 list2) (0, 0 :: Z)
  end <- getTime ProcessCPUTime
  fprint (timeSpecs % "\n") start end


list2 :: Num a => [a]
list2 = concat $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5]

{-myConfig = defaultConfig {
              -- Resample 10 times for bootstrapping
              resamples = 1
           }-}

main = do
  --let (f, c) = mpsHom
  --print $ mpsTest (take 2000 list2) (0, 0 :: Z)
  --print ((fst (parMapRedl c (0, 0 :: Z) f (take 2000 list2))))
  bench ()
  --bench 2
  --bench 3
  --bench 3
  {-defaultMainWith myConfig [ bgroup "mps"[ bench "1 core"  $ nfAppIO (main3) 1
                            , bench "2 cores" $ nfAppIO (main3) 2
                            , bench "3 cores" $ nfAppIO (main3) 3
                            , bench "4 cores" $ nfAppIO (main3) 4
                            -- , bench "8 cores" $ nfAppIO (runWith mpsTest) 8
                            {-, bench "10 cores" $ nf (runWith mpsTest) 10
                            , bench "12 cores" $ nf (runWith mpsTest) 12
                            , bench "14 cores" $ nf (runWith mpsTest) 14
                            , bench "16 cores" $ nf (runWith mpsTest) 16
                            , bench "18 cores" $ nf (runWith mpsTest) 18
                            , bench "20 cores" $ nf (runWith mpsTest) 20-}
                            ]
              ]-}

{-{-# LANGUAGE TemplateHaskell, FlexibleContexts, ViewPatterns, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Control.DeepSeq

import Criterion.Main

import GHC.Conc (setNumCapabilities)

import System.IO.Unsafe

import Conquer

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- +RTS -N16

runWith p num = do
  setNumCapabilities num
  () <- return (rnf (p ()))
  return ()

main = do
  defaultMain [ bgroup "mps"[ bench "1 core"  $ nfIO (runWith mpsTest 1)
                            , bench "2 cores" $ nfIO (runWith mpsTest 2)
                            , bench "4 cores" $ nfIO (runWith mpsTest 4)
                            , bench "6 cores" $ nfIO (runWith mpsTest 6)
                            -- , bench "8 cores" $ nfAppIO (runWith mpsTest) 8
                            {-, bench "10 cores" $ nf (runWith mpsTest) 10
                            , bench "12 cores" $ nf (runWith mpsTest) 12
                            , bench "14 cores" $ nf (runWith mpsTest) 14
                            , bench "16 cores" $ nf (runWith mpsTest) 16
                            , bench "18 cores" $ nf (runWith mpsTest) 18
                            , bench "20 cores" $ nf (runWith mpsTest) 20-}
                            ]
              ]
-}
