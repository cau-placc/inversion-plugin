{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

-- Example from "Principles of Inverse Computation and the Universal Resolving Algorithm"

module Graph2 where

data Node = A | B | C | D
  deriving (Eq, Show)

type Graph = [[Node]]

type Path = [Node]

isWalk :: Graph -> Path -> Bool
isWalk g p = isWalk' p []
  where isInGraph x = x `elem` map head g
        isReachableFrom x y = case lookup y (map (\str -> (head str, tail str)) g) of
          Just ys -> x `elem` ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = x `notElem` (y:ys) && isReachableFrom x y && isWalk' xs (x:y:ys)

graph :: Graph
graph = [ [A,B,C]
        , [B,D]
        , [C]
        , [D,A,C]
        ]

-- Test with:
-- $(partialInv 'isWalk True [0]) graph True (should result in 17 cycle-free walks)
-- $(partialInv 'isWalk True [0]) graph False (should result in an infinite number of cyclic walks)
-- $(partialInv 'isWalk False [0]) graph False (should result in 52/54 representants of cyclic walks)


{-
[Solo "",Solo "a",Solo "b",Solo "c",Solo "d",Solo "ab",Solo "ac",Solo "bd",Solo "da",Solo "dc",Solo "abd",Solo "dab",Solo "bda",Solo "dac",Solo "bdc",Solo "abdc",Solo "bdac"]

[Solo [],Solo [A],Solo [B],Solo [C],Solo [D],Solo [A,B],Solo [A,C],Solo [B,D],Solo [D,C],Solo [A,B,D],Solo [B,D,C],Solo [A,B,D,C]]

Missing: DA, DAB, BDA, DAC, BDAC
Common: subpath: DA
-}
