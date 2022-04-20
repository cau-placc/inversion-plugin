module Par where

import Control.Parallel.Strategies as Par

import Eden.EdenConcHs
import Eden.Map
import Eden.MapReduce

mapRedl :: (a -> b) -> (b -> b -> b) -> b -> [a] -> b
mapRedl f g e = foldl g e . map f

mapRedlPar :: (a -> b) -> (b -> b -> b) -> b -> [a] -> b
mapRedlPar f g e = foldl g e . reducedList . chunkList . withStrategy (parList Par.rseq)
 where
  chunkList []   = []
  chunkList list = let (l,ls) = splitAt 1000 list in l : chunkList ls
  reducedList = Par.parMap Par.rseq (foldl g e . map f)

mapRedlEden :: (Trans a, Trans b) => (a -> b) -> (b -> b -> b) -> b -> [a] -> b
mapRedlEden f g e = parMapRedl g e f
--mapReduceEden f g = parScanl g . map f
