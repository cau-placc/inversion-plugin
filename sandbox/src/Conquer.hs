{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Conquer where

import GHC.Generics

import Eden.EdenConcHs
import Eden.MapReduce

import Plugin.InversionPlugin

import Divide
import Z

deriving instance Generic N
deriving instance Generic Z

instance NFData N
instance NFData Z

instance Trans N
instance Trans Z

-- Maximum prefix/segment sum problem

mpsTupledWI :: _ => _
mpsTupledWI = getSolo . $(weakInv 'mpsTupled True)

mpsHom :: _ => _
mpsHom = (f, c)
  where h = mpsTupled
        f a = h [a]
        hWI = mpsTupledWI
        c a b = h (hWI a ++ hWI b)

mpsTupledWIRef :: _ => _
mpsTupledWIRef (p, s) = [p, s - p]

mpsTest :: _ => _
mpsTest xs e = fst (parMapRedl c e f xs)
  where (f, c) = mpsHom

mpsHomRef :: _ => _
mpsHomRef = (f, c)
  where h = mpsTupled
        f a = h [a]
        hWI = mpsTupledWIRef
        c a b = h (hWI a ++ hWI b)

mssTupledWI :: _ => _
mssTupledWI = getSolo . $(weakInv 'mssTupled True)

mssHom :: _ => _
mssHom = (f, c)
  where h = mssTupled
        f a = h [a]
        hWI = mssTupledWI
        c a b = h (hWI a ++ hWI b)


mssTest :: _ => _
mssTest xs e = fst4 (parMapRedl c e f xs)
  where (f, c) = mssHom
        fst4 (x, _, _, _) = x

mssTupledWIRef :: _ => _
mssTupledWIRef (m, p, t, s) = [p, -p - t - s, m, -m + t]

mssHomRef :: _ => _
mssHomRef = (f, c)
  where h = mssTupled
        f a = h [a]
        hWI = mssTupledWIRef
        c a b = h (hWI a ++ hWI b)


{-e :: (Z, Z)
e = (0, 0)

e2 :: (Integer, Integer, Integer, Integer) -- (Z, Z, Z, Z)
e2 = (0, 0, 0, 0)-}

--list :: Num a => [a]
--list = concat $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5]


-- Line-of-sight problem

visibleTupledWI :: _ => _
visibleTupledWI = getSolo . $(weakInv 'visibleTupled True)

visibleHom :: _ => _
visibleHom = (f, c)
  where h = visibleTupled
        f a = h [a]
        hWI = visibleTupledWI
        c a b = h (hWI a ++ hWI b)

visibleTupledWIRef :: _ => _
visibleTupledWIRef (v, m) | v     && 0 <= m = [0, m]
                          | not v && 0 <= m = [m, 0]

visibleHomRef :: _ => _
visibleHomRef = (f, c)
  where h = visibleTupled
        f a = h [a]
        hWI = visibleTupledWIRef
        c a b = h (hWI a ++ hWI b)


--e3 :: (Bool, Z)
--e3 = (True, 0)

--buildings :: [Z]
--buildings = concat $ take 10000 $ repeat [30,30,20,25,30,15,40,20]
