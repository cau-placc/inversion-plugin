{-# LANGUAGE CPP, BangPatterns, MagicHash, UnboxedTuples #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Parallel.Eden.Merge
-- Copyright   :  (c) Philipps Universitaet Marburg 2012-
-- License     :  BSD-style (see the file LICENSE)
-- 
-- Maintainer  :  eden@mathematik.uni-marburg.de
-- Stability   :  beta
-- Portability :  not portable
--
-- Provides an implementation of nmergeIO (as previously available from
-- Control.Concurrent in base package).
-- Eden language definition assumes merge functionality as a base construct.
--
-- Eden Group Marburg ( http:\/\/www.mathematik.uni-marburg.de/~eden )
-- 
-----------------------------------------------

module Eden.Merge (
 -- * Non-deterministic merge of lists into one result list.  

 -- | Previously available in Concurrent Haskell, living here from GHC-7.6 on.
 -- This function merges incoming lists non-deterministically into one
 -- result. 
 -- Its implementation in this module follows the pattern of the
 -- previous one from Control.Concurrent, but uses the old simple semaphore 
 -- implementation, and optimises the case of only one remaining list. 
 nmergeIO_E
 )
where

#if __GLASGOW_HASKELL__ < 707
import Control.Concurrent(nmergeIO)

nmergeIO_E = nmergeIO

#else

import Control.Concurrent
import Control.Exception( mask_ )
import System.IO.Unsafe

-- simplified version of Control.Concurrent.QSem (as of GHC-7.6)
type QSem_E = MVar (Int,[MVar ()])

newQSem_E :: Int -> IO QSem_E
newQSem_E n | n >= 0    = newMVar (n,[])
            | otherwise = error "QSem: negative."

-- This implementation is prone to losing Q signals in use cases
-- where waiting threads can be killed externally (not the case here).
qsem_P, qsem_Q :: QSem_E -> IO ()
qsem_P sem = mask_ $
             do state <- takeMVar sem
                case state of
                  (0,blocked) -> do b <- newEmptyMVar
                                    putMVar sem (0, blocked ++ [b])
                                    takeMVar b
                  (n,[])      -> putMVar sem (n-1, [])
                  (n,other)   -> error ("QSem: " ++ show (n, length other))
qsem_Q sem = mask_ $ 
             do state <- takeMVar sem
                case state of
                  (n,(blocker:blockers)) -> do putMVar sem (n,blockers)
                                               putMVar blocker ()
                  (n,[])                 -> putMVar sem (n+1, [])

nmergeIO_E :: [[a]] -> IO [a]
nmergeIO_E lss 
    = do let !len = length lss
         tl_node   <- newEmptyMVar
         tl_list   <- newMVar tl_node
         sem       <- newQSem_E 1
         count_var <- newMVar len
         -- start filler threads, one per incoming list
         mapM_ (forkIO . suckIO_E count_var (tl_list, sem) ) lss
         -- deliver result (as soon as first item filled in)
         val <- takeMVar tl_node
         qsem_Q sem
         return val
        
suckIO_E :: MVar Int -> (MVar (MVar [a]),QSem_E) -> [a] -> IO ()
suckIO_E count_var buff@(tl_list,sem) vs
    = do count <- takeMVar count_var
         if count == 1 
            -- last writer, identify own list with result
            then do node <- takeMVar tl_list
                    putMVar node vs
                    putMVar tl_list node
            -- sync with other writers to share 1-space buffer
            else do putMVar count_var count
                    case vs of -- will block until input available
                      -- on end of list, decrease counter
                      []     -> do count <- takeMVar count_var
                                   if count == 1
                                     then do node <- takeMVar tl_list
                                             putMVar node []
                                             putMVar tl_list node
                                     else do putMVar count_var (count-1)
                      -- on new element, add to output list
                      (x:xs) -> do qsem_P sem
                                   node <- takeMVar tl_list
                                   next <- newEmptyMVar
                                   next_val <- unsafeInterleaveIO
                                                 (do y <- takeMVar next
                                                     qsem_Q sem
                                                     return y) 
                                   putMVar node (x:next_val)
                                   putMVar tl_list next
                                   suckIO_E count_var buff xs

#endif