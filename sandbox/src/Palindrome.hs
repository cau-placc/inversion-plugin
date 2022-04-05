{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

-- TODO: Taken from "Principles of Inverse Computation and the Universal Resolving Algorithm" and "Rebuilding a Tree from Its Traversals: A Case Study of Program Inversion"

module Palindrome where

--TODO: mkPalindrome ::

fromPalindromes :: Eq a => [[a]] -> [a]
fromPalindromes xs | all2 (\x -> notNull2 x && isPalindrome x) xs = concat2 xs

isPalindrome :: Eq a => [a] -> Bool
isPalindrome xs = xs == reverse2 xs

--[a] -> [[a]]
fromPalindromesL :: Eq a => [(P, [a])] -> (P, [a])
fromPalindromesL xs | all2 (\(n, x) -> notNull2 x && isPalindromeL n x) xs = concat2L xs

isPalindromeL :: Eq a => P -> [a] -> Bool
isPalindromeL n xs = xs == reverseL n xs
