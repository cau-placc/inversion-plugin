{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

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

genCodeword :: Eq a => Codemap a -> [a] -> [Bool]
genCodeword codemap input = concatMap (maybe loop id . flip lookup codemap) input

encode :: Eq a => [a] -> (Codemap a, [Bool])
encode input = (codemap, codeword)
  where codemap = genCodemap input
        codeword = genCodeword codemap input

--TODO: Remove
loop = loop

--

data Alphabet = A | B | C | D | E | F | G
  deriving (Show, Eq)

--codemap :: Codemap Alphabet
--codemap = genCodemap [A,A,C,E,D,D,F,E,E,B,A,E,F,C,E,A,B,C,C,E]
--word = "Hello World"
word = [A, B, C, C, D, E, D, F, C, G]
codemap = genCodemap word
codeword = genCodeword codemap word

-- Test with: let decode = $(partialInv 'genCodeword True [0]) in decode codemap codeword
-- Interestingly enough, $(inv 'encode True) is not working very well
-- Does also not work very well with primitive types
