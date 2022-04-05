{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module RunLength where

import Peano


rle :: Eq a => [a] -> [(a, Int)]
rle = foldr code []

code :: Eq a => a -> [(a, Int)] -> [(a, Int)]
code c []            = [(c, 1)]
code c ((x, n) : ts) | c == x    = (x, n + 1) : ts
                     | otherwise = (c, 1) : (x, n) : ts



rle2 :: Eq a => [a] -> [(a, Int)]
rle2 [] = []
rle2 (c:cs) = let l = length (takeWhile (== c) cs)
              in (c, l + 1) : rle2 (drop l cs)

rleP :: Eq a => [a] -> [(a, P)]
rleP [] = []
rleP (c:cs) = let l = lengthP (takeWhile (== c) cs)
              in (c, S l) : rleP (dropP l cs)

-- The inverse of `unrleNaive` is not the "right" one as it computes many run-length encodings that have too short sequences in it (or even sequences of length 0).

unrleNaive :: [(a, Int)] -> [a]
unrleNaive = concatMap (uncurry (flip replicate))



unrleNaiveButBetter :: [(a, Int)] -> [a]
unrleNaiveButBetter [] = []
unrleNaiveButBetter ((x, n) : ts) | n > 0 = replicate n x ++ unrleNaiveButBetter ts

unrle :: Eq a => [(a, Int)] -> [a]
unrle [] = []
unrle ((x, n) : []) | n > 0 = replicate n x
unrle ((x, n) : (y, m) : ts) | y /= x && n > 0 = replicate n x ++ unrle ((y, m) : ts)

--TODO: does not work- Segmantation fault for HH
unrle3P :: Eq a => [(a, P)] -> [a]
unrle3P [] = []
unrle3P ((x, n@(S _)) : []) = replicateP n x
unrle3P ((x, n@(S _)) : (y, m) : ts) | y /= x = replicateP n x ++ unrle3P ((y, m) : ts)
unrle3P' :: [(Bool, P)] -> [Bool]
unrle3P' [] = []
unrle3P' ((x, n@(S _)) : []) = replicateP n x
unrle3P' ((x, n@(S _)) : (y, m) : ts) | eqBool y x = replicateP n x ++ unrle3P' ((y, m) : ts)


eqBool False False = True
eqBool True True = True
eqBool _ _ = False

-- $(inv 'unrle3P True) "H" works
-- $(inv 'unrle3P True) "HH" does not

unrle4P :: Eq a => [(a, P)] -> [a]
unrle4P [] = []
unrle4P ((x, S n) : []) = replicateP (S n) x --TODO: singleton pattern
unrle4P ((x, S n) : (y, m) : ts) | y /= x = replicateP (S n) x ++ unrle4P ((y, m) : ts)
--unrle4P _ = absurd

absurd | False = absurd

-- TODO: often functions are pseudo-inverses. for example, the functions rle and unrle are not inverses of each other. unrleInv yields "unexpected" results, like tuples with zero and ('a', 1), ('a', 1) instead of ('a', 2)

--other examples are words/unwords, lines/unlines. zip/unzip. all those functions are not injective.
--(uncurry zip . unzip) gilt, lines "a", "a\n", words mehrere leerzeichen
