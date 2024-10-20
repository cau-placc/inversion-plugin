module Par where

import Eden.EdenConcHs
import Eden.Map
import Eden.MapReduce

mapRedlEden :: (Trans a, Trans b) => (a -> b) -> (b -> b -> b) -> b -> [a] -> b
mapRedlEden f g e = parMapRedl g e f
