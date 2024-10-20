{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Example0 where

data P = Z | S P
  deriving (Show, Eq)

addP Z n = n
addP (S n) m = S (addP n m)

concat2L [] = (Z, [])
concat2L ((n,x):xs) = let (m, ys) = concat2L xs in (addP n m, x ++ ys)

data Alphabet = A | B | C | D | E | F
  deriving (Show, Eq)

reverseL Z _ = (Z, [])
reverseL (S n) (x:xs) = concat2L [reverseL n xs, (S Z, [x])]

{-filter2 :: (a -> Bool) -> [a] -> [a]
filter2 _ [] = []
filter2 p (x:xs) | p x = x : filter2 p xs
                 | otherwise = filter2 p xs
-}
