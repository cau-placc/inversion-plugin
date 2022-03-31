{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

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
          Just ys -> x `elem`ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = isReachableFrom x y && x `notElem` (y:ys) && isWalk' xs (x:y:ys)

graph :: Graph
graph = [ (A, [B,C])
        , (B, [D])
        , (C, [])
        , (D, [A,C])]

-- Test with:
-- $(partialInv 'isWalk True [0]) graph True (should result in 17 cycle-free walks)
-- $(partialInv 'isWalk True [0]) graph False (should result in an infinite number of cyclic walks)
-- $(partialInv 'isWalk False [0]) graph False (should result in 52/54 representants of cyclic walks)
