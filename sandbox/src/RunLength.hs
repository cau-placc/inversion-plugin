{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}

module RunLength where

import Peano

rleNaiveOnePass :: Eq a => [a] -> [(a, Int)]
rleNaiveOnePass = foldr rle' []
  where rle' c []                        = [(c, 1)]
        rle' c ((x, n) : ts) | c == x    = (x, n + 1) : ts
                             | otherwise = (c, 1) : (x, n) : ts

rleNaive :: Eq a => [a] -> [(a, Int)]
rleNaive [] = []
rleNaive (c:cs) = let l = length (takeWhile (== c) cs)
                  in (c, l + 1) : rleNaive (drop l cs)

--TODO: Better variant

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

unrleP :: Eq a => [(a, P)] -> [a]
unrleP [] = []
unrleP ((x, n@(S _)) : []) = replicateP n x
unrleP ((x, n@(S _)) : (y, m) : ts) | y /= x = replicateP n x ++ unrleP ((y, m) : ts)

-- TODO: often functions are pseudo-inverses. for example, the functions rle and unrle are not inverses of each other. unrleInv yields "unexpected" results, like tuples with zero and ('a', 1), ('a', 1) instead of ('a', 2)

--other examples are words/unwords, lines/unlines. zip/unzip. all those functions are not injective.
--(uncurry zip . unzip) gilt, lines "a", "a\n", words mehrere leerzeichen
