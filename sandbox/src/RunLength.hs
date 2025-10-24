{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin -fforce-recomp #-}

module RunLength where

--TODO: Add paper (which one?)
--TODO num instanz

-- [('h',S Z),('a',S Z),('l',S (S Z)),('o',S Z),('w',S Z),('e',S Z),('l',S Z),('t',S Z)]

import P

rle :: Eq a => [a] -> [(a, Int)]
rle = foldr rle' []
  where rle' c ((x, n) : ts) | c == x && n > 0= (x, n + 1) : ts
        rle' c ts                     = (c, 1) : ts

rle2 :: Eq a => [a] -> [(a, Int)]
rle2 [] = []
rle2 (c:cs) = let l = length (takeWhile (== c) cs)
              in (c, l + 1) : rle2 (drop l cs)

rle3 :: Eq a => [a] -> [(a, Int)]
rle3 [] = []
rle3 (c:cs) = let l = length (takeWhile (== c) cs)
              in (c, l + 1) : rle3 (dropWhile (== c) cs)

--TODO: Better variant, that terminates?

rleP :: Eq a => [a] -> [(a, P)]
rleP [] = []
rleP (c:cs) = let l = lengthP (takeWhile (== c) cs)
              in (c, S l) : rleP (dropP l cs)


-- [(A,2),(A,0),(A,1)]
-- The inverses of `unrleNaive` and `unrleNaiveButBetter`are not the "right" ones as they computes run-length encodings that have too short sequences in it (or even sequences of length 0 in case of `unrleNaive`).

-- man ist es nicht gewohnt zu invertieren, instruktiv (aber unabhöngig vom system)

unrleNaive :: [(a, Int)] -> [a]
unrleNaive = concatMap (uncurry (flip replicate))

unrleNaiveButBetter :: [(a, Int)] -> [a]
unrleNaiveButBetter [] = []
unrleNaiveButBetter ((x, n) : ts) | n > 0 = replicate n x ++ unrleNaiveButBetter ts

{-
replicate 0 _ = []
replicate n x = x : replicate (n - 1) x
-}

-- The following correct inverse of `rle` does not terminate.
unrle :: Eq a => [(a, Int)] -> [a]
unrle [] = []
unrle ((x, n) : []) | n > 0 = replicate n x
unrle ((x, n) : (y, m) : ts) | y /= x && n > 0 = replicate n x ++ unrle ((y, m) : ts)

-- However, using Peano numbers helps w.r.t. termination.
unrleP :: Eq a => [(a, P)] -> [a]
unrleP [] = []
unrleP ((x, n@(S _)) : []) = replicateP n x
unrleP ((x, n@(S _)) : (y, m) : ts) | y /= x = replicateP n x ++ unrleP ((y, m) : ts)

-- TODO: often functions are pseudo-inverses. for example, the functions rle and unrle are not inverses of each other. unrleInv yields "unexpected" results, like tuples with zero and ('a', 1), ('a', 1) instead of ('a', 2)

--other examples are words/unwords, lines/unlines. zip/unzip. all those functions are not injective.
--(uncurry zip . unzip) gilt, lines "a", "a\n", words mehrere leerzeichen
