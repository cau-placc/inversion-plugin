{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

-- TODO: Taken from "Principles of Inverse Computation and the Universal Resolving Algorithm" and "Rebuilding a Tree from Its Traversals: A Case Study of Program Inversion"

module TreeTraversal where

-- Test with: $(inv 'inorder True) [7, 6, 5, 4, 3, 2, 1]

data Tree a = Empty
            | Node (Tree a) a (Tree a)
  deriving Show

preorder :: Tree a -> [a]
preorder Empty        = []
preorder (Node l x r) = [x] ++ preorder l ++ preorder r

inorder :: Tree a -> [a]
inorder Empty        = []
inorder (Node l x r) = inorder l ++ [x] ++ inorder r

{-
inorderInv []
inorder 0
-> { 0 -> Empty } inorder Empty -> []
-> { 0 -> Node 1 2 3 } inorder (Node 1 2 3) -> inorder 1 ++ [2] ++ inorder 3
-> { 1 -> Empty } inorder Empty ++ [2] ++ inorder 3 -> [] ++ [2] ++ inorder 3
-> { 1 -> Node 4 5 6 } [] ++ [] ++ [] ++ []
-}


splits :: [a] -> [([a], [a])]
splits [] = [([], [])]
splits (x:xs) = ([], x:xs) : map (\(ys, zs) -> (x:ys, zs)) (splits xs)

{-
inorderInv :: [a] -> [Tree a]
inorderInv [] = [Empty]
inorderInv (inorder l ++ ([x] ++ inorder r)) = Node l x r

inorderInv :: [a] -> [Tree a]
inorderInv [] = [Empty]
inorderInv zs = concatMap (\(inorder l, [x] ++ inorder r) -> [Node l x r]) (splits zs)

inorderInv zs = concatMap (\(zs1, [x] ++ inorder r) -> concatMap (\l -> [Node l x r]) (inorderInv l))) (splits zs)

inorderInv zs = concatMap (\(zs1, zs2) -> concatMap (\l -> concatMap (\([x], zs3) -> concatMap (\r -> [Node l x r]) (inorderInv zs3)) (splits zs2)) (inorderInv zs1))) (splits zs)
-}
inorderInv :: [a] -> [Tree a]
inorderInv [] = [Empty]
inorderInv zs = concatMap (\(zs1, zs2) -> concatMap (\l -> concatMap (\(xs, zs3) -> case xs of {[x] -> concatMap (\r -> [Node l x r]) (inorderInv zs3); _ -> []}) (splits zs2)) (inorderInv zs1)) (splits zs)

-- Inverse of pinorder does terminate despite the fact that the inverse of inorder does not terminate.

pinorder :: Tree a -> ([a], [a])
pinorder t = (preorder t, inorder t)

-- Inverse of inporder does not terminate, because the inverse of inorder does not terminate.

inporder :: Tree a -> ([a], [a])
inporder t = (inorder t, preorder t)

exampleTree :: Tree Char
exampleTree = Node (Node (Node Empty 'a' Empty) 'b' (Node Empty 'c' Empty)) 'd' (Node (Node Empty 'e' Empty) 'f' Empty)
