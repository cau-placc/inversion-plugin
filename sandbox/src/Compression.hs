{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Compression where

import Prelude hiding (span, head, length, concatMap)
import Peano

data Chr = A | B | C | O | I | II | III
  deriving (Show, Eq)

showP :: Peano -> Chr
showP Z = O
showP (S Z) = I
showP (S (S Z)) = II
showP (S (S (S Z))) = III

instance Show Peano where
  show x = show (peanoToIntegral x)

peanoToIntegral :: (Num i) => Peano -> i
peanoToIntegral Z     = 0
peanoToIntegral (S n) = 1 + peanoToIntegral n

intToChr :: Int -> Chr
intToChr i = case i of
  0 -> O
  1 -> I
  2 -> II
  3 -> III

encode2 :: String -> String
encode2 "" = ""
encode2 (x:xs) = x : encode2' x (S Z) xs
  where
    encode2' :: Char -> Peano -> String -> String
    encode2' c n [] = show n
    encode2' c n (y:ys) | c == y = encode2' c (S n) ys
                        | True   = show n `app` ([y] `app` encode2' y (S Z) ys)

-- encode2 :: [Chr] -> [Chr]
-- encode2 [] = []
-- encode2 (x:xs) = x : encode2' x (S Z) xs
--   where encode2' c n [y] | c == y = [showP (S n)]
--                          | True = [showP n, y, I]
--         encode2' c n (y:ys) | c == y = encode2' c (S n) ys
--                             | True   = showP n : y : encode2' y (S Z) ys

encode :: [Chr] -> [Chr]
encode s = concatMap (\xs -> [head xs, showP (lengthPeano xs)]) (group s)

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap _ [] = []
concatMap f (x:xs) = app (f x) (concatMap f xs)

app :: [a] -> [a] -> [a]
app [] xs = xs
app (x:xs) ys = x : (app xs ys)

group                   :: Eq a => [a] -> [[a]]
group                   =  groupBy (==)

groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []           =  []
groupBy eq (x:xs)       =  (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs

span                    :: (a -> Bool) -> [a] -> ([a],[a])
span _ xs@[]            =  (xs, xs)
span p xs@(x:xs')
         | p x          =  let (ys,zs) = span p xs' in (x:ys,zs)
         | True    =  ([],xs)

head :: [a] -> a
head (x:_) = x

-- length :: [a] -> Int
-- length [] = 0
-- length (_:xs) = 1 + length xs

-- encode :: String -> String
-- encode s = concatMap (group s)

-- concatMap :: [String] -> String
-- concatMap [] = []
-- concatMap (x:xs) = app (head x : showInt (length x)) (concatMap xs)

-- app :: [a] -> [a] -> [a]
-- app [] xs = xs
-- app (x:xs) ys = x : (app xs ys)

-- group              :: Eq a => [a] -> [[a]]
-- group []           =  []
-- group (x:xs)       =  (x:ys) : group zs
--                         where (ys,zs) = span x xs

-- span                   :: Eq a => a -> [a] -> ([a],[a])
-- span _ xs@[]            =  (xs, xs)
-- span p xs@(x:xs')
--          | p == x  =  let (ys,zs) = span p xs' in (x:ys,zs)
--          | True    =  ([],xs)

-- head :: [a] -> a
-- head (x:_) = x

-- length :: [a] -> Int
-- length [] = 0
-- length (_:xs) = 1 + length xs
