{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Match where

---TODO: substring/match from the URA: inverse computation in a functional language

import P

match :: Eq a => [a] -> [a] -> Bool
match [] _      = True
match _  []     = False
match xs (y:ys) = take (length xs) (y:ys) == xs || match xs ys

matchP :: Eq a => [a] -> [a] -> Bool
matchP [] _      = True
matchP _  []     = False
matchP xs (y:ys) = takeP (lengthP xs) (y:ys) == xs || matchP xs ys

matchAlt :: Eq a => [a] -> [a] -> Bool
matchAlt [] _      = True
matchAlt _  []     = False
matchAlt xs (y:ys) = match' xs (y:ys) || matchAlt xs ys
  where match' [] _ = True
        match' (x:xs) (y:ys) = x == y && match' xs ys
        match' _ _ = False

-- $(partialInv 'match [1]) "abcd" True
-- \x -> $(clsInv 'match [ free 1, "abcd" ] (x))

-- concrete example from "principles of inverse computation and the URA"
