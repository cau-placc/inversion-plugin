{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

-- This example is from the paper "Principles of Inverse Computation and the Universal Resolving Algorithm" by Sergei Abramov and Robert Glück.

-- This example from "Principles of Inverse Computation and the Universal Resolving Algorithm" and "Rebuilding a Tree from Its Traversals: A Case Study of Program Inversion"

module TreeTraversal where

data Tree a = Empty
            | Node (Tree a) a (Tree a)
  deriving Show

preorder :: Tree a -> [a]
preorder Empty        = []
preorder (Node l x r) = [x] ++ preorder l ++ preorder r

inorder :: Tree a -> [a]
inorder Empty        = []
inorder (Node l x r) = inorder l ++ [x] ++ inorder r

inporder :: Tree a -> ([a], [a])
inporder t = (inorder t, preorder t)

pinorder :: Tree a -> ([a], [a])
pinorder t = (preorder t, inorder t)
exampleTree :: Tree Char
exampleTree = Node (Node (Node Empty 'a' Empty) 'b' (Node Empty 'c' Empty)) 'd' (Node (Node Empty 'e' Empty) 'f' Empty)

-- Tests:

-- $(inv 'inorder) [7, 6, 5, 4, 3, 2, 1]
-- Returns all solutions, but does not terminate.

-- $(partialInv 'inorder' [0]) (depth exampleTree) (inorder exampleTree)
-- Returns all solutions and does terminate.

-- $(inv 'preorder) [7, 6, 5, 4, 3, 2, 1]
-- Returns all solutions.

-- $(inv 'inporder) (inporder exampleTree)
-- Finds one solution, but does terminate because of the non-termination of the inverse of inorder, which gets computed first.

-- $(inv 'pinorder) (pinorder exampleTree)
-- Finds one solution and terminates because the inverse of preorder, which gets computed first, terminates.


depth :: Tree a -> Int
depth Empty        = 0
depth (Node l _ r) = 1 + max (depth l) (depth r)

inorder' :: Int -> Tree a -> [a]
inorder' n Empty        | n >= 0 = []
inorder' n (Node l x r) | n > 0  = inorder' (n - 1) l ++ [x] ++ inorder' (n - 1) r
