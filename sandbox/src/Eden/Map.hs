{-# LANGUAGE CPP, ScopedTypeVariables #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Parallel.Eden.Map
-- Copyright   :  (c) Philipps Universitaet Marburg 2009-2014
-- License     :  BSD-style (see the file LICENSE)
-- 
-- Maintainer  :  eden@mathematik.uni-marburg.de
-- Stability   :  beta
-- Portability :  not portable
--
-- This Haskell module defines map-like skeletons for 
-- the parallel functional language Eden.
--
-- Depends on GHC. Using standard GHC, you will get a threaded simulation of Eden. 
-- Use the forked GHC-Eden compiler from http:\/\/www.mathematik.uni-marburg.de/~eden 
-- for a parallel build.
--
-- Eden Group ( http:\/\/www.mathematik.uni-marburg.de/~eden )


module Eden.Map (
                 -- * Custom map skeletons 
                 -- | These skeletons expose many parameters to the user and thus have varying types
                 parMap, ranch, 
                 farm, farmS, farmB, 
                 offlineFarm, offlineFarmS, offlineFarmB,
                 -- * Custom map skeletons with explicit placement
                 -- | Map skeleton versions with explicit placement
                 parMapAt, ranchAt, farmAt, offlineFarmAt, 
                 -- * Simple map skeleton variants 
                 -- | The map skeletons 'farm' and 'offlineFarm' can be used to define 
                 --  skeletons with the simpler sequential map interface :: (a -> b) -> [a] -> [b]
                 mapFarmB, mapFarmS, mapOfflineFarmS, mapOfflineFarmB,
                 -- * Deprecated map skeletons
                 -- | These skeletons are included to keep old code alive. Use the skeletons above.
                 farmClassic, ssf, offline_farm, map_par, map_farm, map_offlineFarm, map_ssf
                 ) where
import Eden.EdenConcHs
import Eden.Auxiliary
import Data.List


-- | Basic parMap Skeleton - one process for each list element. This version takes 
-- places for instantiation on particular PEs. 
parMapAt :: (Trans a, Trans b) => 
            Places      -- ^places for instantiation          
            -> (a -> b) -- ^worker function
            -> [a]      -- ^task list
            -> [b]      -- ^result list
parMapAt pos f tasks = spawnAt pos (repeat (process f)) tasks


-- | Basic parMap Skeleton - one process for each list element
parMap :: (Trans a, Trans b) => 
          (a -> b)   -- ^worker function
          -> [a]     -- ^task list
          -> [b]     -- ^result list
parMap = parMapAt [0]


-- | A process ranch is a generalized (or super-) farm. This version takes 
-- places for instantiation. Arbitrary input is transformed into a list of inputs 
-- for the worker processes (one worker for each transformed value). The worker 
-- inputs are processed by the worker function.
-- The results of the worker processes are then reduced using the reduction function.
ranchAt :: (Trans b, Trans c) => 
           Places         -- ^places for instantiation
           -> (a -> [b])  -- ^input transformation function 
           -> ([c] -> d)  -- ^result reduction function
           -> (b -> c)    -- ^worker function
           -> a           -- ^input 
           -> d           -- ^output
ranchAt pos transform reduce fs xs = 
        reduce $ spawnAt pos (repeat $ process fs) (transform xs)

-- | A process ranch is a generalized (or super-) farm.  Arbitrary input 
-- is transformed into a list of inputs for the worker processes (one worker 
-- for each transformed value). The worker inputs are processed by the worker function.
-- The results of the worker processes are then reduced using the reduction function.
ranch :: (Trans b, Trans c) => 
         (a -> [b])     -- ^input transformation function 
         -> ([c] -> d)  -- ^result reduction function
         -> (b ->  c)   -- ^worker function
         -> a           -- ^input 
         -> d           -- ^output
ranch = ranchAt [0]


-- | A farm distributes its input to a number of worker processes.
-- This version takes places for instantiation.
-- The distribution function divides the input list into 
-- sublists - each sublist is input to one worker process, the 
-- number of worker processes is determined by the number of 
-- sublists. The results of the worker processes are 
-- then combined using the combination function.
-- 
-- Use 'map_farm' if you want a simpler interface.
--
farmAt :: (Trans a, Trans b) => 
          Places            -- ^places for instantiation
          -> ([a] -> [[a]]) -- ^input distribution function 
          -> ([[b]] -> [b]) -- ^result combination function
          -> (a ->  b)      -- ^mapped function
          -> [a]            -- ^input 
          -> [b]            -- ^output
farmAt pos distr combine f tasks = ranchAt pos distr combine (map f) tasks

-- | A farm distributes its input to a number of worker processes.
-- The distribution function divides the input list into 
-- sublists - each sublist is input to one worker process, the 
-- number of worker processes is determined by the number of 
-- sublists. The results of the worker processes are 
-- then combined using the combination function.
-- 
-- Use 'mapFarmS' or 'mapFarmB' if you want a simpler interface.
--
farm :: (Trans a, Trans b) => 
        ([a] -> [[a]])    -- ^input distribution function 
        -> ([[b]] -> [b]) -- ^result combination function
        -> (a ->  b)      -- ^mapped function
        -> [a]            -- ^input 
        -> [b]            -- ^output
farm = farmAt [0]

-- | Like the 'farm', but uses a fixed round-robin distribution of tasks.
farmS :: (Trans a, Trans b) 
         => Int            -- ^number of processes
         -> (a ->  b)      -- ^mapped function
         -> [a]            -- ^input 
         -> [b]            -- ^output
farmS np = farm (unshuffle  np) shuffle

-- | Like the 'farm', but uses a fixed block distribution of tasks.
farmB :: (Trans a, Trans b) 
         => Int            -- ^number of processes
         -> (a ->  b)      -- ^mapped function
         -> [a]            -- ^input 
         -> [b]            -- ^output
farmB np = farm (splitIntoN np) concat




-- | Offline farm with explicit placement (alias self-service farm or
-- direct mapping): Like the farm, but tasks are evaluated inside the
-- workers (less communication overhead). Tasks are mapped inside each
-- generated process abstraction, avoiding evaluating and sending
-- them. This often reduces the communication overhead because
-- unevaluated data is usually much smaller than evaluated data.
-- 
-- Use 'map_offlineFarm' if you want a simpler interface.
--
-- Notice: The task lists structure has to be completely defined
-- before process instantiation takes place.
--
offlineFarmAt :: Trans b => 
         Places            -- ^places for instantiation
         -> Int            -- ^number of processes
         -> ([a] -> [[a]]) -- ^input distribution function 
         -> ([[b]] -> [b]) -- ^result combination function
         -> (a ->  b)      -- ^mapped function
         -> [a]            -- ^input 
         -> [b]            -- ^output

offlineFarmAt pos np distribute combine f xs 
  = combine $ spawnAt pos (map (rfi (map f)) [select i xs | i <- [0 .. np-1]])
                          (repeat ())
  where select i xs = (distribute xs ++ repeat []) !! i



-- | Offline farm (alias direct mapping): Like the farm, but
-- tasks are evaluated inside the workers (less communication
-- overhead). Tasks are mapped inside each generated process
-- abstraction avoiding evaluating and sending them. This often
-- reduces the communication overhead because unevaluated data is
-- usually much smaller than evaluated data.
-- 
-- Use 'map_offlineFarm' if you want a simpler interface.
--
-- Notice: The offline farm receives the number of processes to be created
-- as its first parameter. 
-- The task lists structure has to be completely defined
-- before process instantiation takes place.
--
offlineFarm :: Trans b => 
       Int               -- ^number of processes 
       -> ([a] -> [[a]]) -- ^input distribution function 
       -> ([[b]] -> [b]) -- ^result combination function
       -> (a ->  b)      -- ^mapped function
       -> [a]            -- ^input 
       -> [b]            -- ^output

offlineFarm  = offlineFarmAt [0]

-- | Like the 'offlineFarm', but with fixed round-robin distribution of tasks.
offlineFarmS :: (Trans a, Trans b) 
                => Int            -- ^number of processes
                -> (a ->  b)      -- ^mapped function
                -> [a]            -- ^input 
                -> [b]            -- ^output
offlineFarmS np = offlineFarm np (unshuffle np) shuffle

-- | Like the 'offlineFarm', but with fixed block distribution of tasks.
offlineFarmB :: (Trans a, Trans b) 
                => Int            -- ^number of processes
                -> (a ->  b)      -- ^mapped function
                -> [a]            -- ^input 
                -> [b]            -- ^output
offlineFarmB np = offlineFarm np (splitIntoN np) concat


------------------------------------------------------------------------------------
numProc = max (noPe-1) 1

-- | Parallel map variant with map interface using (max (noPe-1) 1) worker processes. Skeletons ending on @S@ use round-robin distribution, skeletons ending on @B@ use block distribution of tasks.
mapFarmS, mapFarmB, mapOfflineFarmS, mapOfflineFarmB :: (Trans a , Trans b) => 
                             (a -> b)   -- ^worker function
                             -> [a]     -- ^task list
                             -> [b]     -- ^result list 
mapFarmS        = farmS numProc
mapFarmB        = farmB numProc
mapOfflineFarmS = offlineFarmS numProc
mapOfflineFarmB = offlineFarmB numProc

-----------------------------DEPRECATED---------------------------------


-- | Deprecated, use the 'farm';
-- @farmClassic@ distributes its input to a number of worker processes.
-- This is the Classic version as described in the Eden standard reference 
-- "Parallel Functional Programming in Eden".
-- The distribution function is expected to divide the input list into 
-- the given number of sublists. In the new farm the number of sublists is 
-- determined only by the distribution function.
-- 
-- Use 'map_farm' if you want a simpler interface.
{-# DEPRECATED farmClassic "better use farm instead" #-}
farmClassic :: (Trans a, Trans b) => 
               Int                      -- ^number of child processes
               -> (Int -> [a] -> [[a]]) -- ^input distribution function 
               -> ([[b]] -> [b])        -- ^result combination function
               -> (a ->  b)             -- ^mapped function
               -> [a]                   -- ^input 
               -> [b]                   -- ^output

farmClassic np distribute = farm $ distribute np


-- | Deprecated, use 'offlineFarm'; 
-- Self service farm. Like the farm, but
-- tasks are evaluated in the workers (less communication overhead).
-- This is the classic version. The distribution function is expected
-- to divide the input list into the given number of sublists. In the
-- new self service farm the number of sublists is determined only by
-- the distribution function.
-- 
-- Use 'map_ssf' if you want a simpler interface.
--
-- Notice: The task lists structure has to be completely defined
-- before process instantiation takes place.
{-# DEPRECATED ssf "better use offlineFarm instead" #-}
ssf :: forall a b . Trans b => 
       Int                          -- ^number of child processes
       -> (Int -> [a] -> [[a]])     -- ^input distribution function 
       -> ([[b]] -> [b])            -- ^result combination function
       -> (a ->  b)                 -- ^mapped function
       -> [a]                       -- ^input 
       -> [b]                       -- ^output

ssf np distribute = offlineFarm np (distribute np) 

-- | Deprecated: Same as 'offlineFarm'.
{-# DEPRECATED offline_farm "better use offlineFarm instead" #-}
offline_farm :: Trans b => 
       Int               -- ^number of processes 
       -> ([a] -> [[a]]) -- ^input distribution function 
       -> ([[b]] -> [b]) -- ^result combination function
       -> (a ->  b)      -- ^mapped function
       -> [a]            -- ^input 
       -> [b]            -- ^output
offline_farm = offlineFarm

-- | Deprecated: Same as 'parMap'.
{-# DEPRECATED map_par "better use parMap instead" #-}
map_par :: (Trans a , Trans b) => 
                             (a -> b)   -- ^worker function
                             -> [a]     -- ^task list
                             -> [b]     -- ^result list 
map_par         = parMap

-- | Deprecated: Parallel map variants with map interface using noPe worker processes.
{-# DEPRECATED map_farm, map_offlineFarm, map_ssf "better use mapFarmS or mapOfflineFarmS instead" #-}
map_farm, map_offlineFarm, map_ssf :: (Trans a , Trans b) => 
                             (a -> b)   -- ^worker function
                             -> [a]     -- ^task list
                             -> [b]     -- ^result list 
map_farm        = farmS noPe
map_offlineFarm = offlineFarmS noPe
map_ssf         = map_offlineFarm