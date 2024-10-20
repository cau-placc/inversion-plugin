{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Egison where

import Prelude hiding (map)

-- insert :: a -> [a] -> [[a]
-- insert x [] = [[x]]
-- insert x (y:ys) = (x:y:ys) : (map (y:) (insert x ys))

-- map :: (a -> b) -> [a] -> [b]
-- map _ [] = []
-- map f (x:xs) = f x : map f xs

insert :: a -> [a] -> [a]
insert x [] = [x]
insert x (y:ys) = x:y:ys `app` (y:(insert x ys))

app :: [a] -> [a] -> [a]
app [] xs = xs
app (x:xs) ys = x : (app xs ys)

infixr 7 `app`

appPat2 :: [Int] -> Int -> [Int] -> [Int] -> [Int]
appPat2 u1 x u2 u3 = u1 `app` [x] `app` u2 `app` [x + 1] `app` u3

appPat3 :: [Int] -> Int -> [Int] -> [Int] -> [Int] -> [Int]
appPat3 u1 x u2 u3 u4 = 
    u1 `app` [x] `app` u2 `app` [x + 1] `app` u3 `app` [x + 2] `app` u4

appPat4 :: [Int] -> Int -> [Int] -> [Int] -> [Int] -> [Int] -> [Int]
appPat4 u1 x u2 u3 u4 u5 = 
    u1 `app` [x] `app` u2 `app` [x + 1] 
       `app` u3 `app` [x + 2] `app` u4 `app` [x + 3] `app` u5