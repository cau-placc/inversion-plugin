{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Peano where

data P = Z | S P
  deriving (Eq, Ord, Show)

addP :: P -> P -> P
addP Z     n = n
addP (S m) n = S (addP m n)

lengthP :: [a] -> P
lengthP []     = Z
lengthP (_:xs) = S (lengthP xs)

replicateP :: P -> a -> [a]
replicateP Z     _ = []
replicateP (S n) x = x : replicateP n x

takeP Z     _      = []
takeP _     []     = []
takeP (S n) (x:xs) = x : takeP n xs

dropP :: P -> [a] -> [a]
dropP Z     xs     = xs
dropP (S l) (_:xs) = dropP l xs
