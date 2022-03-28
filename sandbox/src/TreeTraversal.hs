{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

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

-- Inverse of pinorder does terminate despite the fact that the inverse of inorder does not terminate.

pinorder :: Tree a -> ([a], [a])
pinorder t = (preorder t, inorder t)

-- Inverse of inporder does not terminate, because the inverse of inorder does not terminate.

inporder :: Tree a -> ([a], [a])
inporder t = (inorder t, preorder t)

exampleTree :: Tree Char
exampleTree = Node (Node (Node Empty 'a' Empty) 'b' (Node Empty 'c' Empty)) 'd' (Node (Node Empty 'e' Empty) 'f' Empty)
