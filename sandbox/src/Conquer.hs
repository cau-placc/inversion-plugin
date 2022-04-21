{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module Conquer where

import Plugin.InversionPlugin

import Divide
import Par
import Z

import GHC.Generics

import Eden.EdenConcHs

deriving instance Generic N
deriving instance Generic Z
instance Trans N
instance Trans Z
instance NFData N
instance NFData Z

{-mpsTupledWI :: (Z, Z) -> [Z]
mpsTupledWI = getSolo . $(weakInv 'mpsTupled True)

mpsTupledWIRef :: (Z, Z) -> [Z]
mpsTupledWIRef (p, s) = [p, s - p]

mssTupledWI :: (Z, Z, Z, Z) -> [Z]
mssTupledWI = getSolo . $(weakInv 'mssTupled True)

mssTupledWIRef :: (Z, Z, Z, Z) -> [Z]
mssTupledWIRef (m, p, t, s) = [p, -p - t - s, m, -m + t]-}

mpsTupledWI :: _ => _
mpsTupledWI = getSolo . $(weakInv 'mpsTupled True)

mpsTupledWIRef :: _ => _
mpsTupledWIRef (p, s) = [p, s - p]

mssTupledWI :: _ => _
mssTupledWI = getSolo . $(weakInv 'mssTupled True)

mssTupledWIRef :: _ => _
mssTupledWIRef (m, p, t, s) = [p, -p - t - s, m, -m + t]

visibleTupledWI :: _ => _
visibleTupledWI = getSolo . $(weakInv 'visibleTupled True)

mpsHom :: _ => _
mpsHom = (f, c)
  where h = mpsTupled
        f a = h [a]
        hWI = mpsTupledWI
        c a b = h (hWI a ++ hWI b)

mpsHomRef :: _ => _
mpsHomRef = (f, c)
  where h = mpsTupled
        f a = h [a]
        hWI = mpsTupledWIRef
        c a b = h (hWI a ++ hWI b)

mssHom :: _ => _
mssHom = (f, c)
  where h = mssTupled
        f a = h [a]
        hWI = mssTupledWI
        c a b = h (hWI a ++ hWI b)

mssHomRef :: _ => _
mssHomRef = (f, c)
  where h = mssTupled
        f a = h [a]
        hWI = mssTupledWIRef
        c a b = h (hWI a ++ hWI b)

visibleHom :: _ => _
visibleHom = (f, c)
  where h = visibleTupled
        f a = h [a]
        hWI = visibleTupledWI
        c a b = h (hWI a ++ hWI b)

fst4 (x, _, _, _) = x

-- Test with: test1X [1,-2,2,1]
-- let xs = [1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1,-2,2,1]
test1 xs e = fst (mapRedl f c e xs)
  where (f, c) = mpsHom

test1Par xs e = fst (mapRedlPar f c e xs)
  where (f, c) = mpsHom

test1Eden xs e = fst (mapRedlEden f c e xs)
  where (f, c) = mpsHom

test2Eden xs e = fst4 (mapRedlEden f c e xs)
  where (f, c) = mssHom

test3Eden xs = map fst (scanlEden c (map f xs))
  where (f, c) = visibleHom

--test1Eden xs =

test1Ref xs e = fst (mapRedl f c e xs)
  where (f, c) = mpsHomRef

test1RefPar xs e = fst (mapRedlPar f c e xs)
  where (f, c) = mpsHomRef

test1RefEden xs e = fst (mapRedlEden f c e xs)
  where (f, c) = mpsHomRef

test2RefEden xs e = fst4 (mapRedlEden f c e xs)
  where (f, c) = mssHomRef
