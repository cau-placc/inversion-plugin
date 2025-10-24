{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

-- Example from "Principles of Inverse Computation and the Universal Resolving Algorithm"

module Graph where

data Node = A | B | C | D
  deriving (Eq, Show)

type Graph = [(Node, [Node])]

type Path = [Node]

isWalk :: Graph -> Path -> Bool
isWalk g p = isWalk' p []
  where isInGraph x = x `elem` map fst g
        isReachableFrom x y = case lookup y g of
          Just ys -> x `elem` ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = x `notElem` (y:ys) && isReachableFrom x y && isWalk' xs (x:y:ys)

graph :: Graph
graph = [ (A, [B,C])
        , (B, [D])
        , (C, [])
        , (D, [A,C])]

-- Tests:

-- $(partialInv 'isWalk [0]) graph True (should result in 17 cycle-free walks)

-- $(partialInv 'isWalk [0]) graph False (should result in an infinite number of cyclic walks)

-- map showFree $ $(partialInvFree 'isWalk [0]) graph False
-- This should result in 52 representants of cyclic walks. The original paper spoke of 54 solutions, but never listed the actual values.
-- This seems to be an error in the original paper (we spoke with the author).
