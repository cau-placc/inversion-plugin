{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

-- This example is from the paper "Principles of Inverse Computation and the Universal Resolving Algorithm" by Sergei Abramov and Robert Glück.

module Graph where

data Node = A | B | C | D
  deriving (Eq, Show)

type Graph a = [(a, [a])]

type Path a = [a]

-- This function checks whether a given path is a cycle-free walk in the given graph.
isWalk :: Eq a => Graph a -> Path a -> Bool
isWalk g p = isWalk' p []
  where isInGraph x = x `elem` map fst g
        isReachableFrom x y = case lookup y g of
          Just ys -> x `elem` ys
        isWalk' []     _      = True
        isWalk' (x:xs) []     | isInGraph x = isWalk' xs [x]
        isWalk' (x:xs) (y:ys) | isInGraph x = x `notElem` (y:ys) && isReachableFrom x y && isWalk' xs (x:y:ys)

exampleGraph :: Graph Node
exampleGraph = [ (A, [B,C])
               , (B, [D])
               , (C, [])
               , (D, [A,C])
               ]

exampleGraphPrimitive :: Graph Char
exampleGraphPrimitive = [ ('A', "BC")
                        , ('B', "D")
                        , ('C', "")
                        , ('D', "AC")
                        ]

-- Tests:

-- ghci> $(partialInv 'isWalk [1]) exampleGraph True
-- ghci> $(partialInv 'isWalk [1]) exampleGraphPrimitive True
-- These terminate and result in 17 cycle-free walks.
-- However, the primitive version runs longer due to the overhead of the constraint solver for primitive types.

-- ghci> map showFree $ $(partialInvFree 'isWalk [1]) exampleGraph False
-- ghci> map showFree $ $(partialInvFree 'isWalk [1]) exampleGraphPrimitive False
-- These terminate and result in 52 values that do not represent cycle-free walks.
-- The original paper spoke of 54 solutions, but never listed the actual values.
-- This seems to be an error in the original paper (we spoke with one of the authors).
-- Again, the primitive version runs longer due to the overhead of the constraint solver for primitive types.

-- ghci> $(partialInv 'isWalk [1]) exampleGraph False
-- ghci> $(partialInv 'isWalk [1]) exampleGraphPrimitive False
-- These result in infinite lists of values that do not represent cycle-free walks.
-- Each value is an instantiation of one of the 52 values returned by the examples above.
