{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

-- This example demonstrates, using Huffman encoding as a case study, how partial inversion can be used to derive a decoder from an encoder.

module Huffman where

data HTree a = HLeaf a Int
             | HNode (HTree a) (HTree a) Int
  deriving Show

weight :: HTree a -> Int
weight (HLeaf _ w)   = w
weight (HNode _ _ w) = w

partition :: (a -> Bool) -> [a] -> ([a], [a])
partition p = foldr select ([], [])
  where select x (xs,ys) | p x = (x : xs, ys)
                         | otherwise = (xs, x : ys)

frequencies :: Eq a => [a] -> [(a, Int)]
frequencies []     = []
frequencies (x:xs) = let (ys, zs) = partition (== x) xs
                     in (x, length ys + 1) : frequencies zs

type Codemap a = [(a, [Bool])]

orderedInsert :: HTree a -> [HTree a] -> [HTree a]
orderedInsert t []                              = [t]
orderedInsert t (t':ts) | weight t <= weight t' = t : t' : ts
                        | otherwise             = t' : orderedInsert t ts

makeTree :: [HTree a] -> HTree a
makeTree [t]       = t
makeTree (t:t':ts) = makeTree (orderedInsert (HNode t t' (weight t + weight t')) ts)

makeCodemap :: HTree a -> Codemap a
makeCodemap (HLeaf x _)    = [(x, [])]
makeCodemap (HNode l r _)  = map (addBit False) (makeCodemap l) ++ map (addBit True) (makeCodemap r)
  where addBit b (x, y) = (x, b : y)

genCodemap :: Eq a => [a] -> Codemap a
genCodemap input = makeCodemap (makeTree (map (uncurry HLeaf) (frequencies input)))

encode :: Eq a => Codemap a -> [a] -> [Bool]
encode codemap word = concatMap (maybe (error "cannot encode unknown letter") id . flip lookup codemap) word

data Alphabet = A | B | C | D | E | F | G
  deriving (Eq, Show)

word :: [Alphabet]
word = [A, B, C, C, D, E, D, F, C, G]

codemap :: Codemap Alphabet
codemap = genCodemap word

codeword :: [Bool]
codeword = encode codemap word

wordPrimitive :: String
wordPrimitive = "abccdedfcg"

codemapPrimitive :: Codemap Char
codemapPrimitive = genCodemap wordPrimitive

codewordPrimitive :: [Bool]
codewordPrimitive = encode codemapPrimitive wordPrimitive

-- Tests:

-- $(inv 'encode) is not the right choice for the definition for a decoding function.
-- The (correct) inverse of encode would be a function that returns pairs of codemaps and words that would result in the given codeword.
-- However, there would be an infinite number of solutions for this.
-- For a decoding function, we want to use the knowledge of the codemap to decode the codeword.
-- We can do so by using the partially inverted function of encode, where we fix the codemap argument.
-- Therefore, we use the following definition:
-- let decode = $(partialInv 'encode [0]) codemap in decode codeword

-- We provide the same test with primitive types. It works fine, but it is a lot slower than the version with the custom type.
-- let decodePrimitive = $(partialInv 'encode [0]) codemapPrimitive in decodePrimitive codewordPrimitive
