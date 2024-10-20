{-# LANGUAGE TemplateHaskell, FlexibleContexts, ViewPatterns, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Main where

import Criterion.Main

import GHC.Conc (getNumProcessors, getNumCapabilities, setNumCapabilities)

import Conquer

fib :: Int -> Int
fib 0 = 0
fib 1 = 1
fib n = fib (n-1) + fib (n-2)

-- Build with: stack build sandbox:main --flag inversion-plugin:use-what4
-- Run with: time stack exec main -- +RTS -N16

main = do
  numCores <- getNumProcessors
  putStrLn $ "Number of cores available: " ++ show numCores
  getNumCapabilities >>= \num -> putStrLn ("Number of threads used: " ++ show num)
  setNumCapabilities 4
  getNumCapabilities >>= \num -> putStrLn ("Number of threads used: " ++ show num)
  print (test1Eden list e)
  defaultMain [
       bgroup "fib" [ bench "10" $ whnf fib 10
                    , bench "35" $ whnf fib 35
                    , bench "37" $ whnf fib 37
                    ]
                   ]
  --print ((map fst . scanl1 (snd visibleHom)) $ map (fst visibleHom) buildings)
  --print (map visible (myinits buildings)) --(test3Eden buildings e3)

e :: (Z, Z)
e = (0, 0)

e2 :: (Integer, Integer, Integer, Integer) --} (Z, Z, Z, Z)
e2 = (0, 0, 0, 0)

e3 :: (Bool, Z)
e3 = (True, 0)

buildings :: [Z]
buildings = concat $ take 10000 $ repeat [30,30,20,25,30,15,40,20]

list :: [Z]
list = take 2000 $ concat $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]
--list = [1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1]

{---f = map showFree $ ($(inOutClassInv 'id False [[| Test True True |]] [| var 2 |]) :: [Solo Test])

split :: _ => _
split = $(inv '(++) True)

split123 :: [([Int], [Int])]
split123 = split [1,2,3]

--anythingBut42 :: [Int]
--anythingBut42 = $(inv 'is42) False

--last :: Invertible a => [a] -> a
--last $(funPat '(++) [p| _ |] [p| [x] |]) = x
--last _ = error "empty list"

--TODO: impossible to give type signature as FL is not exported (and should not be)
--TODO: Maybe use "Inverted" = "Lifted FL"
--reverseLookup :: (Invertible a, Invertible b, Eq a, Lifted FL (Eq a))
--              => [(a, b)] -> Maybe b -> [a]
reverseLookup :: _ => _
reverseLookup = $(partialInv 'lookup True [1])

testMap :: [(Int, Maybe Bool)]
testMap = [(0, Nothing), (2, Just False)]

--hasDuplicates :: Invertible a => [a] -> Bool
--hasDuplicates $(funPat 'hasDuplicatesPat [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = True
--hasDuplicates _ = False

--isSame :: Invertible a => (a, a) -> Bool
--isSame $(funPat 'dup [p| _ |]) = True
--isSame _                       = False
-}
