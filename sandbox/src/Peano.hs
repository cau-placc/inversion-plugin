{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Peano where

data Peano = Z | S Peano

type P = Peano

isZero:: Peano -> Bool
isZero = (== Z)

isNotZero:: P -> Bool
isNotZero = (/= Z)

instance Eq Peano where
  Z == Z = True
  S n == S m = n == m
  _ == _ = False

add :: Peano -> Peano -> Peano
add Z     n = n
add (S m) n = S (add m n)

lengthPeano :: [a] -> Peano
lengthPeano [] = Z
lengthPeano (_:xs) = S (lengthPeano xs)
