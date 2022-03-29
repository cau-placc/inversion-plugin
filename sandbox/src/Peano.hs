{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Peano where

data Peano = Z | S Peano

isZero:: Peano -> Bool
isZero = (== Z)

isNotZero:: Peano -> Bool
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

replicateP :: Peano -> a -> [a]
replicateP Z _ = []
replicateP (S n) x = x : replicateP n x

unrle3P :: Eq a => [(a, Peano)] -> [a]
unrle3P [] = []
unrle3P [(x, S n)] = replicateP (S n) x
unrle3P ((x, S n) : (y, m) : ts) | y /= x = replicateP (S n) x ++ unrle3P ((y, m) : ts)