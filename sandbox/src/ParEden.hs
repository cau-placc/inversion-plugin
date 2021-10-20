{-# LANGUAGE DeriveGeneric, StandaloneDeriving, ScopedTypeVariables, ExplicitForAll #-}

module ParEden where

import Par

import Data.List (inits, tails)

import Plugin.InversionPlugin

import Eden.EdenConcHs
import Eden.Map
import Eden.MapReduce

import GHC.Generics

deriving instance Generic N
deriving instance Generic Z
instance Trans N
instance Trans Z
instance NFData N
instance NFData Z

--testList = [1,-1,2]
--testList = [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5]
--testListZ = [Pos I,Neg I,Pos (S I)]
--testListZ = [Pos I,Neg I,Pos (S I),Neg I,Neg (S I),Pos (S (S I)),Neg (S I),Pos (S (S (S (S I)))),Neg (S (S (S (S I)))),Neg I,Neg (S (S (S (S I)))),Pos (S I),Pos (S I),Neg (S (S (S (S I))))]
--testList = [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]
testList = take 8 $ concat $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]
testListZ = take 8 $ map toZ $ concat $ repeat [1,-1,2,-1,-2,3,-2,2,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]
--testListZ = map toZ [1,-1,2,-1,-2,3,-2,5,-2,-1,-2,2] -- ,2,-5] -- ,1,-1,2] -- ,-1,-2,3,-2,5 ] -- ,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]

toZ :: Integer -> Z
toZ x | x == 0 = Zero
      | x > 0  = Pos $ toN x
      | otherwise = Neg $ toN (negate x)

toN :: Integer -> N
toN 1 = I
toN n = S (toN (pred n))

fromZ :: Z -> Integer
fromZ Zero = 0
fromZ (Pos n) = fromN n
fromZ (Neg n) = negate $ fromN n

fromN :: N -> Integer
fromN I = 1
fromN (S n) = succ $ fromN n

ref = mps testList

h = (f, c)
  where f a = (mymax 0 a, a)
        c (px, sx) (py, sy) = mpsSum ([px, sx - px] ++ [py, sy - py])
h2 = (f, c)
  where f a = mpsSum2 [a]
        hWI = $(weakInv 'mpsSum2)
        c a b = mpsSum2 (hWI a ++ hWI b)


h3 = (f, c) --mssTupled
  where f a = mssTupled [a]
        hWI = $(weakInv 'mssTupled)
        c a b = mssTupled (hWI a ++ hWI b)
h3' = (f, c) --mssTupled
  where f a = mssTupled [a]
        hWI = mssTupledWI
        c a b = mssTupled (hWI a ++ hWI b)
h4 = (f, c) --mssTupled
  where f a = mssZTupled [a]
        hWI = $(weakInv 'mssZTupled)
        c a b = mssZTupled (hWI a ++ hWI b)
h5 = (f, c)
  where f a = mpsZTupled [a]
        --hWI = mpsZTupledWI
        hWI = $(weakInv 'mpsZTupled)
        c a b = mpsZTupled (hWI a ++ hWI b)
h6 = (f, c)
  where f a = sumZ [a]
        hWI = $(weakInv 'sumZ)
        c a b = sumZ (hWI a ++ hWI b)
h7 :: forall a. Invertible a => (a -> Z, Z -> Z -> Z)
h7 = (f, c)
  where f a = lengthZ [a]
        hWI = $(weakInv 'lengthZ) :: Z -> [a]
        c a b = lengthZ (hWI a ++ hWI b)
{-
h8 = (f, c)
  where f a = mysort [a]
        hWI = $(weakInv 'mysort)
        c a b = mysort (hWI a ++ hWI b)
        -}
h9 = (f, c)
  where f a = visibleTupled [a]
        hWI = $(weakInv 'visibleTupled)
        c a b = visibleTupled (hWI a ++ hWI b)
h10 = (f, c)
  where f a = visibleZTupled [a]
        hWI = $(weakInv 'visibleZTupled)
        c a b = visibleZTupled (hWI a ++ hWI b)

myinits = tail . inits --without []

parScanl c = parMap (foldl1 c) . myinits
myscanl c = map (foldl1 c) . myinits

seqTest = (\(a, _, _, _) -> a) $ mssTupled testList
  where (f, c) = h3
--parTest = (\(a, _, _, _) -> a) $ parMapRedr c (0, 0, 0, 0) f testList
--  where (f, c) = h3
--seqTest = (\(a, _, _, _) -> fromZ a) $ mssZTupled testListZ
--parTest = (\(a, _) -> fromZ a) $ parMapRedr c (Zero, Zero) f testListZ
--  where (f, c) = h5
--parTest = fromZ $ parMapRedr c Zero f testListZ
--  where (f, c) = h7
--parTest = parMapRedr c [] f testList
--  where (f, c) = h8
parTest = map fst $ parScanl c $ map (f . toZ) $ take 500 $ concat $ repeat [30,30,20,25,30,15,40,20] --[1,2,2,3,5,4,7,6]
  where (f, c) = h10