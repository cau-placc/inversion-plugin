module ParUse where

import Par

import Plugin.InversionPlugin

import Data.List (foldl')

import Control.Parallel.Strategies

--testList = [1,-1,2]
--testList = [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5]
testList = concat $ take 10000 $ repeat [1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3,-2,5,-5,-1,-5,2,2,-5,1,-1,2,-1,-2,3]

ref = mps testList

reduce = foldr1

{-h = (f, c)
  where f a = mps [a]
        hWI = $(weakInv 'mps)
        c a b = mps (hWI a ++ hWI b)

-- This is the wrong application, because mps cannot be written both leftwards and rightwards. (at least not using the same structure as it would be required)

seqVer = reduce c . map f
  where (f, c) = h
seqTest = seqVer testList-}


parMapReduce :: (a -> b) -> (b -> b -> b) -> b -> [a] -> b
parMapReduce f o e = foldl' o e . reducedList . chunkList . withStrategy (parList rseq)
 where
  chunkList [] = []
  chunkList list = let (l,ls) = splitAt 1000 list in l : chunkList ls
  reducedList = parMap rseq (foldl' o e . map f)


h2 = (f, c)
  where f a = mpsSum [a]
        hWI = $(weakInv 'mpsSum)
        c a b = mpsSum (hWI a ++ hWI b)

h3' = (f, c) --mssTupled
  where f a = mssTupled [a]
        hWI = mssTupledWI
        c a b = mssTupled (hWI a ++ hWI b)

mpsSeq = fst . reduce c . map f
  where (f, c) = h2
seqTest = mpsSeq testList

mpsParaReal = parMapReduce f c (0,0,0,0) --fst . reduce c . parMap rpar f
  where (f, c) = h3'
parTest = mpsParaReal testList

--TODO: hilft nicht, da das reduce das aufwändige ist. das muss parallelisert werden. Also muss wohl eden ran.