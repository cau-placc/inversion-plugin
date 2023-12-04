{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module P where

data P = Z | S P
  deriving (Eq, Ord, Show)

toP :: Int -> P
toP 0 = Z
toP i | i > 0 = S (toP (i - 1))

fromP :: P -> Int
fromP Z     = 0
fromP (S n) = 1 + fromP n

addP :: P -> P -> P
addP Z     n = n
addP (S m) n = S (addP m n)

subP :: P -> P -> P
subP n     Z     = n
subP (S n) (S m) = subP n m

incP :: P -> P
incP n = S n

decP :: P -> P
decP (S m) = m

multP :: P -> P -> P
multP Z     _ = Z
multP (S m) n = addP n (multP n m)

lengthP :: [a] -> P
lengthP []     = Z
lengthP (_:xs) = S (lengthP xs)

mapP :: P -> (a -> b) -> [a] -> [b]
mapP Z     f []     = []
mapP (S n) f (x:xs) = f x : mapP n f xs

replicateP :: P -> a -> [a]
replicateP Z     _ = []
replicateP (S n) x = x : replicateP n x

takeP :: P -> [a] -> [a]
takeP Z     _      = []
takeP _     []     = []
takeP (S n) (x:xs) = x : takeP n xs

dropP :: P -> [a] -> [a]
dropP Z     xs     = xs
dropP (S l) (_:xs) = dropP l xs
