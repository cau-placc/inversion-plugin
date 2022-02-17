{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module Tree where

data Tree a = Empty
            | Node (Tree a) a (Tree a)
  deriving Show

preorder :: Tree a -> [a]
preorder Empty        = []
preorder (Node l x r) = [x] ++ preorder l ++ preorder r

inorder :: Tree a -> [a]
inorder Empty        = []
inorder (Node l x r) = inorder l ++ [x] ++ inorder r

pinorder :: Tree a -> ([a], [a])
pinorder t = (preorder t, inorder t)

inporder :: Tree a -> ([a], [a])
inporder t = (inorder t, preorder t)
