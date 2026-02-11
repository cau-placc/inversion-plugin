{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module ToBeInverted where

myAppend :: [a] -> [a] -> [a]
myAppend []     ys = ys
myAppend (x:xs) ys = x : myAppend xs ys

myLookup :: Eq k => k -> [(k, v)] -> Maybe v
myLookup k []          = Nothing
myLookup k ((k',v):xs)
  | k == k'   = Just v
  | otherwise = myLookup k xs
