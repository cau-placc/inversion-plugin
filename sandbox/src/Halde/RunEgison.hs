{-# LANGUAGE TemplateHaskell, StandaloneDeriving, FlexibleContexts, ExtendedDefaultRules, ViewPatterns, ScopedTypeVariables #-}
module RunEgison where

import Egison

import Plugin.InversionPlugin

--seq2 :: Invertible a => [a] -> String
seq2  $(funPat 'insert [p| x |] [p| $(funPat 'insert [p| x |] [p| _ |]) |]) = "Matched"
seq2 _ = "Not matched"

test :: Int -> [()]
test 0 = []
test n = insert () (test (n-1))

-- f (_ ++ [x] ++ _ ++ [x + 1] ++ _) = True

app2 $(funPat 'appPat2 [p| _ |] [p| x |] [p| _ |] [p| _ |]) = "Matched"
app2 _ = "Not matched"

app3 $(funPat 'appPat3 [p| _ |] [p| x |] [p| _ |] [p| _ |] [p| _ |]) = "Matched"
app3 _ = "Not matched"

app4 $(funPat 'appPat4 [p| _ |] [p| x |] [p| _ |] [p| _ |] [p| _ |] [p| _ |]) = "Matched"
app4 _ = "Not matched"

gen n = concatMap (\m -> m : take n (repeat 42)) [0..10]
