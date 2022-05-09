{-# OPTIONS_GHC -fno-full-laziness #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Main where

import Control.DeepSeq

--import Criterion.Main
--import Criterion.Types

import Data.Time

import Eden.EdenConcHs
import Eden.MapReduce
import GHC.Generics
import Z

import GHC.Conc (setNumCapabilities)

import System.Environment

import Conquer

deriving instance Generic N
deriving instance Generic Z

instance NFData N
instance NFData Z

instance Trans N
instance Trans Z

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

bench n = do
  setNumCapabilities n
  start <- getCurrentTime
  let (f, c) = mpsHom
  () <- return $ rnf (fst (parMapRedl c (0, 0 :: Z) f (take 2000 list)))
  end <- getCurrentTime
  print (diffUTCTime end start)


list :: Num a => [a]
list = concat $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5]

{-myConfig = defaultConfig {
              -- Resample 10 times for bootstrapping
              resamples = 1
           }-}

main = do
  bench 2
  bench 2
  bench 3
  bench 3
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
