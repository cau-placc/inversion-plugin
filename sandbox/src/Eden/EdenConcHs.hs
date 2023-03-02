{-# OPTIONS -XCPP -XDeriveGeneric #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Control.Parallel.Eden.EdenConcHs
-- Copyright   :  (c) Philipps Universitaet Marburg 2005-2012
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  eden@mathematik.uni-marburg.de
-- Stability   :  beta
-- Portability :  not portable
--
-- Provides functions for semi-explicit distributed functional programming.
-- Defines high-level coordination concepts via Prim.Op.s (which are wrapped
-- inside ParPrimConc.hs).
--
-- Notice: This module uses the concurrent simulation of the
-- parallel primitives.
--
-- Depends on GHC.
--
-- Eden Group Marburg ( http:\/\/www.mathematik.uni-marburg.de/~eden )
--


module Eden.EdenConcHs(
        -- * Basic Eden
        -- ** Process definition
        Process, process, rfi
        -- ** Parallel Action
        , PA() , runPA
        -- ** Process instantiation
        -- | The operator # is the standard operator for process instantiation in Eden. Similar
        -- to applying a function @f@ to an argument @x@ (@f x@), it instantiates
        -- a process for f with the argument x (process f # x). The computation is
        -- the same from a denotational point of view. The operational semantics,
        -- however, is different because the operation is executed remotely. If
        -- you prefer to expose the side effects of such an operation explicitly with the
        -- IO-Monad wrapped in the parallel action monad, you can use function @instantiate@
        -- (p # x = runPA (instantiate p x)). It is non-trivial to instantiate
        -- a list of processes such that all instantiations take place immediately. Therefore Eden
        -- provides function @spawn@ which wraps this commonly used pattern.
        --
        -- The Eden runtime system handles process placementfor the basic instantiation functions.
        -- In the default setting, process placement is done round robin,
        -- where the distribution is decided locally by each machine. The runtime option @qrnd@
        -- enables random process placement. Eden further offers functions instantiateAt and
        -- spawnAt with an additional placement parameter. @instantiateAt i@ instantiates the
        -- process at machine @i mod noPe@ for a positive @i@ and @instantiateAt 0 = instantiate@.
        -- This is similar for @spawnAt@.
        --
        -- All instantiation functions are also provided in versions which take functions instead
        -- of process abstractions as parameters. In this case, the process abstractions are
        -- implicitly created prior to instantiation. The function version of @#@ is e.g. called @$#@,
        -- the names of other instantiation functions of this kind contain an @F@.
        , ( # )
   , ( $# )
        , spawn
        , spawnF
        , spawnAt
        , spawnFAt
        , instantiate
   , instantiateF
        , instantiateAt     -- explicit placement
        , instantiateFAt     -- explicit placement
        -- ** Overloaded Communication
        -- | Communication of process inputs and outputs is done implicitly by the Eden runtime system.
        -- The sent data has to be transmissible i.e. it has to be an instance of type class Trans. All
        -- data will be evaluated to normal form before it is sent in one message. Communication is
        -- overloaded for lists which are sent as streams element by element, and for tuples which are
        -- sent using concurrent channel connections for each tuple element. Note that lists in
        -- tuples are streamed concurrently, but a list of tuples
        -- is streamed element-wise, with each tuple elements evaluated as a whole.
        -- The inner list of nested lists will also be sent in one packet.
   , Trans(..)
        -- * Explicit placement
   , noPe, selfPe, Places
   -- * Remote Data
-- | A remote data handle @ RD a @ represents data of type a which may be located on a remote machine. Such a handle is very small and can be passed via intermediate machines with only little communication overhead. You can create a remote data using the function
-- release and access a remote value using the function fetch.
--
-- Notice that a remote value may only be fetched exactly once!
        , RD
        , release, releasePA, fetch, fetchPA
        , releaseAll, fetchAll
        , liftRD, liftRD2, liftRD3, liftRD4
        -- * Dynamic Channels
   , ChanName          -- Communicator a -> IO(), abstract outside
   , new, parfill      -- using unsafePerformIO
   -- * Nondeterminism
   , merge, mergeProc  -- merge, as specified in Eden language, but function!
        -- * Deprecated legacy code for Eden 5
   , Lift(..), deLift, createProcess, cpAt
   -- * Reexported functions from Control.Deepseq
   , NFData(..)
        -- * Reexported functions from Control.Seq (strategies differ from those in Control.Parallel!)
        , Strategy, using, r0, rseq, rdeepseq, seqList, seqFoldable --frequently used
        -- * Reexported functions from Control.Parallel
        , pseq
        )
    where

import Control.Concurrent      -- Instances only
import System.IO.Unsafe(unsafePerformIO) -- for functional face
import qualified Eden.ParPrimConcHs as ParPrim
import Eden.ParPrimConcHs hiding(noPe,selfPe)
import Control.DeepSeq (NFData(..))
import Control.Seq -- reexported!
        (Strategy, using, r0, rseq, rdeepseq, seqList, seqFoldable)

import Control.Parallel(pseq)

import Eden.Merge

import GHC.Generics

import Data.Typeable

--------------------------
-- legacy code for Eden 5:

{-# DEPRECATED deLift, Lift "Lift data type not needed in Eden 6 implementation" #-}
data Lift a = Lift a
deLift :: Lift a -> a
deLift (Lift x) = x

{-# DEPRECATED createProcess "better use instantiate :: Process a b -> a -> IO b instead" #-}
createProcess :: (Trans a, Trans b)
       => Process a b -> a -> Lift b
createProcess p i = runPA (instantiate p i >>= \x -> return (Lift x))

cpAt :: (Trans a, Trans b)
       => Int -> Process a b -> a -> Lift b
cpAt pe p i = runPA (instantiateAt pe p i >>= \x -> return (Lift x))

--------------------parallel action monad--------------------------

newtype PA a = PA { fromPA :: IO a }

instance Functor PA where
  fmap f (PA i) = PA $ fmap f i

instance Applicative PA where
  pure b = PA $ return b
  PA f <*> PA x = PA $ f <*> x


instance Monad PA where
 (PA ioX) >>= f = PA $ do
   x  <- ioX
   fromPA $ f x

runPA :: PA a -> a
runPA = unsafePerformIO . fromPA


-------------- Eden constructs, also available in seq. version ----------

-- explicit placement

-- | Number of (logical) machines in the system
noPe :: Int
noPe = unsafePerformIO ParPrim.noPe

-- | Local machine number (ranges from 1 to noPe)
selfPe :: Int
selfPe = unsafePerformIO ParPrim.selfPe

-- | Places where to instantiate lists of processes
type Places = [Int]

-- processes and instantiation

-- | Creates a process abstraction @ Process a b @ from a function @ a -> b@.
process       :: (Trans a, Trans b)
                 => (a -> b)     -- ^ Input function
                 -> Process a b  -- ^ Process abstraction from input function
process f = Proc f_remote
    where f_remote (Comm sendResult) inCC
            = do    (sendInput, input) <- createComm
                    connectToPort inCC
                    sendData Data sendInput
                    sendResult (f input)

-- | Remote function invocation, evaluating a function application remotely
-- without communicating the input argument
rfi     :: Trans b
           => (a -> b)     -- ^ Input function
           -> a            -- ^ Offline input
           -> Process () b -- ^ Process abstraction; process takes unit input
rfi h x =  process (\ () -> h x)

-- | Instantiates a process on a remote machine, sends the input
--  of type a and returns the process output of type b in the parallel action monad, thus it can be combined to a larger parallel action.
instantiate   :: (Trans a, Trans b) => Process a b -- ^Process abstraction
                  -> a                             -- ^Process input
                  -> PA b                          -- ^Process output
instantiate = instantiateAt 0


-- | Instantiation with explicit placement (see instantiate).
instantiateAt :: (Trans a, Trans b) => Int -- ^Machine number
                 -> Process a b            -- ^Process abstraction
                 -> a                      -- ^Process input
                 -> PA b                   -- ^Process output
instantiateAt p (Proc f_remote) procInput
    = PA $ do
                (sendResult,  r  )     <- createComm  -- result communicator
                (inCC, Comm sendInput) <- createC     -- reply: input communicator
                sendData (Instantiate p)
                    (f_remote sendResult inCC)
                fork (sendInput procInput)
                return r


-- combined processes creation and instantiation
-- | Instantiates a process defined by the given function on a remote machine, sends the input
--  of type a and returns the process output of type b in the parallel action monad, thus it can be combined to a larger parallel action.
instantiateF   :: (Trans a, Trans b) => (a -> b)   -- ^Function for Process
                  -> a                             -- ^Process input
                  -> PA b                          -- ^Process output
instantiateF     = (instantiateAt 0) . process



-- | Instantiation with explicit placement (see instantiate).
instantiateFAt :: (Trans a, Trans b) => Int -- ^ Machine number
                 -> (a -> b)               -- ^Process abstraction
                 -> a                      -- ^Process input
                 -> PA b                   -- ^Process output
instantiateFAt p = instantiateAt p . process


-- | Instantiates a process abstraction on a remote machine, sends the input
--  of type a and returns the process output of type b.

( # )         :: (Trans a, Trans b)
                 => Process a b        -- ^Process abstraction
                 -> a                  -- ^Process input
                 -> b                  -- ^Process output
{-# NOINLINE ( # ) #-}
p # x = runPA $ instantiateAt 0 p x


-- | Instantiates a process defined by the given function on a remote machine, sends the input
--  of type a and returns the process output of type b.

( $# )         :: (Trans a, Trans b)
                 => (a -> b)           -- ^Process abstraction
                 -> a                  -- ^Process input
                 -> b                  -- ^Process output
{-# NOINLINE ( $# ) #-}
f $# x = runPA $ instantiateAt 0 (process f) x       -- better defined directly because of NOINLINE ( # )?

-- | Instantiates a list of process abstractions on remote machines
--  with corresponding inputs of type a and returns the processes
--  outputs, each of type b. The i-th process is supplied with the
--  i-th input generating the i-th output.
--  The number of processes (= length of output list) is determined by
--  the length of the shorter input list (thus one list may be infinite).
spawn :: (Trans a,Trans b)
         => [Process a b] -- ^Process abstractions
         -> [a]           -- ^Process inputs
         -> [b]           -- ^Process outputs
{-# NOINLINE spawn #-}
spawn = spawnAt [0]


-- | Same as @ spawn @ , but with an additional @[Int]@ argument that specifies
--  where to instantiate the processes.
spawnAt :: (Trans a,Trans b)
           => [Int]          -- ^Machine numbers
           -> [Process a b]  -- ^Process abstractions
           -> [a]            -- ^Process inputs
           -> [b]            -- ^Process outputs
{-# NOINLINE spawnAt #-}
spawnAt pos ps is
    = runPA $
           sequence
              [instantiateAt st p i |
              (st,p,i) <- zip3 (cycle pos) ps is]

-- | Instantiates processes defined by the given list of functions on remote machines
--  with corresponding inputs of type a and returns the processes
--  outputs, each of type b. The i-th process is supplied with the
--  i-th input generating the i-th output.
--  The number of processes (= length of output list) is determined by
--  the length of the shorter input list (thus one list may be infinite).
spawnF :: (Trans a,Trans b)
         => [a -> b]      -- ^Process abstractions
         -> [a]           -- ^Process inputs
         -> [b]           -- ^Process outputs
{-# NOINLINE spawnF #-}
spawnF           =  spawnAt [0] . map process


-- | Same as @ spawnF @ , but with an additional @[Int]@ argument that specifies
--  where to instantiate the processes.
spawnFAt :: (Trans a,Trans b)
           => [Int]          -- ^ Machine numbers
           -> [a -> b]       -- ^Process abstractions
           -> [a]            -- ^Process inputs
           -> [b]            -- ^Process outputs
{-# NOINLINE spawnFAt #-}
spawnFAt pos     = spawnAt pos . map process



-- | Process abstractions of type @ Process a b @ can be created with function
-- @process@. Process abstractions define remote functions similar to lambda
-- abstractions, which define local functions.
data Process a b
    = Proc (ChanName b ->             -- send back result, overloaded
       ChanName' (ChanName a) -> -- send input Comm., not overloaded
       IO ()
      )


----------------- merge function, borrowed from Concurrent Haskell -------
-- | Non-deterministically @merge@s a list of lists (usually input streams)
-- into a single list. The order of the output list is determined by the
-- availability of the inner lists constructors. (Function merge is defined
-- using a list merge function @nmergeIO_E@) (similar to nmergeIO from
-- Concurrent Haskell, but in a custom version).
merge :: [[a]]  -- ^ Input lists
         -> [a] -- ^ Nondeterministically merged output list
merge xss = unsafePerformIO (nmergeIO_E xss)

-- | same as @ merge @
mergeProc :: [[a]]  -- ^ Input lists
             -> [a] -- ^ Nondeterministically merged output list
mergeProc = merge

---------------------------------------
-- overloading trick: a "communicator" provides a suitable
-- communication function for the overloaded type

-- type Comm a = (a -> IO())
-- JB20061017: leads to obscure runtime errors
-- Must use an own data type like this:

newtype Comm a = Comm (a -> IO())
  deriving Generic
-- assumed: contained function sends a over a (previously wired-in) channel
instance NFData (Comm a)

-- | A channel name @ChanName a@ is a handle for a reply channel. The channel
-- can be created with the function new and you can connect to such a channel
-- with the function @parfill@.
type ChanName a = Comm a -- provide old Eden interface to the outside world

----------------------------
-- Eden-specific operations new/parfill for dynamic channels:

{-# NOINLINE new #-}
-- | A channel can be created with the function new (this is an unsafe side
-- effect!). It takes a function whose
-- first parameter is the channel name @ChanName a@ and whose second parameter
-- is the value of type a that will be received lazily in the future. The
-- @ChanName@ and the value of type a can be used in the body of the parameter
-- function to create the output of type @b@. The output of the parameter
-- function will be forwarded to the output of @ new @ .
--
-- Example:
-- @new (\channame val -> (channame,val))@
-- returns the tuple @(channame, value)@ .
new :: Trans a =>
       (ChanName a -> a-> b)  -- ^ Parameter function that takes a channel name and a substitute for the lazily received value.
       -> b        -- ^ Forwarded result
new chanValCont = unsafePerformIO $ do
   (chan , val) <- createComm
   return (chanValCont chan val)

{-# NOINLINE parfill #-}
-- | You can connect to a reply channel with function @parfill@ (this is an
-- unsafe side effect!). The first parameter is the name of the channel, the
-- second parameter is the value to be send. The third parameter will be the
-- functions result after the
-- concurrent sending operation is initiated. The sending operation will be
-- triggered as soon as the result of type @b@ is demanded. Take care not to
-- make the result of @parfill@ depend on the sent value, as this
-- will create a deadlock.
parfill :: Trans a => ChanName a -- ^ @ChanName@ to connect with
           -> a                  -- ^ Data that will be send
           -> b                  -- ^ Forwarded to result
           -> b                  -- ^ Result (available after sending)

parfill (Comm sendVal) val cont
    = unsafePerformIO (fork (sendVal val) >> return cont)

------------------------------------------------------------------------
--Remote Data Def


type RD a = ChanName (ChanName a)

-- | Converts local data into corresponding remote data.
{-# NOINLINE release #-}
release :: Trans a => a -- ^ The original data
           -> RD a      -- ^ The Remote Data handle
release = runPA . releasePA


-- | This establishes a direct connection to the process which released the data in the first place.
-- Notice that a remote value may only be fetched exactly once!
{-# NOINLINE fetch #-}
fetch   :: Trans a
           => RD a   -- ^ The Remote Data handle
           -> a      -- ^ The original data
fetch = runPA . fetchPA


-- | Converts local data into corresponding remote data. The result is in the parallel action monad and can be combined to a larger parallel action.
releasePA :: Trans a
            => a            -- ^ The original data
            -> PA (RD a)    -- ^ The Remote Data handle
releasePA val = PA $ do
  (cc , Comm sendValC) <- createComm
  fork (sendValC val)
  return cc


-- | This establishes a direct connection to the process which released the data in the first place. The result is in the parallel action monad and can be combined to a larger parallel action.
-- Notice that you have to fetch a remote value exactly once!
fetchPA   :: Trans a => RD a -> PA a
fetchPA (Comm sendValCC) = PA $ do
  (c,val) <- createComm
  fork (sendValCC c)
  return val


-- | Transforms a list of local data into a corresponding remote data list.
{-# NOINLINE releaseAll #-}
releaseAll :: Trans a
              => [a]    -- ^ The original data
              -> [RD a] -- ^ The Remote Data handles, one for each list element
releaseAll as = runPA $ mapM releasePA as

-- | Transforms a list of remote data into a corresponding local data list.
-- @map fetch@ would wait for each list element until fetching the next one.
-- Function @fetchAll@ blocks only on partial defined list structure, not on content.
{-# NOINLINE fetchAll #-}
fetchAll :: Trans a
            => [RD a] -- ^ The Remote Data handles
            -> [a]    -- ^ The original data
fetchAll ras = runPA $ mapM fetchPA ras


-- | Function @liftRD@ is used to lift functions acting
-- on normal data to function performing the same computation on Remote Data.
liftRD :: (Trans a, Trans b)
          => (a -> b) -- ^ Function to be lifted
          -> RD a     -- ^ Remote input
          -> RD b     -- ^ Remote output
liftRD f = release . f . fetch

-- | see @liftRD@
liftRD2 :: (Trans a, Trans b, Trans c)
           => (a -> b -> c)  -- ^ Function to be lifted
           -> RD a   -- ^ First remote input
           -> RD b   -- ^ Second remote input
           -> RD c   -- ^ Remote output
liftRD2 f x = liftRD (f  (fetch x))

-- | see @liftRD@
liftRD3 :: (Trans a, Trans b, Trans c, Trans d) => (a -> b -> c -> d) -> RD a -> RD b -> RD c -> RD d
liftRD3 f x = liftRD2 (f  (fetch x))

-- | see @liftRD@
liftRD4 :: (Trans a, Trans b, Trans c, Trans d, Trans e) => (a -> b -> c -> d -> e) -> RD a -> RD b -> RD c -> RD d -> RD e
liftRD4 f x = liftRD3 (f  (fetch x))
------------------------------------------------------------------------------------
-- | Trans class: overloads communication for streams and tuples.
-- You need to declare normal-form evaluation in an instance declaration of NFData.
-- Use the default implementation for @write@ and @createComm@ for instances of Trans.
class (NFData a, Typeable a) => Trans a where
    write :: a -> IO ()
    write x = rdeepseq x `pseq` sendData Data x
--    write x = unEval $
--              do x' <- rdeepseq x
--                 return (sendData Data x')

    createComm :: IO (ChanName a, a)
    createComm = do (cx,x) <- createC
                    return (Comm (sendVia cx) , x)

---------------------------------------
-- Trans Instances:
-------------------

-- "standard types" from Prelude are Transmissible with default
-- communication
instance Trans Int
instance Trans Float
instance Trans Double
instance Trans Char
instance Trans Integer
instance Trans Bool

instance Trans a  => Trans (Maybe a)
instance (Trans a,Trans b)  => Trans (Either a b)

instance Trans ()
-- unit: no communication desired? BREAKS OLD PROGRAMS
-- where
--     write () = error "Eden.lhs: writing unit value"
--     createComm = return (Comm (\_ -> return ()), ())

-- stream communication:
instance (Trans a, Typeable a) => Trans [a]  where
    write l@[]   = sendData Data l
    --    write (x:xs) = (rnf x `seq` sendData Stream x) >>
    write (x:xs) = (write' x) >> write xs
      where
        write' x = rdeepseq x `pseq` sendData Stream x


-- "higher-order channels"
instance (NFData a, Trans a) => Trans (Comm a)

-- tuple instances:
instance (Trans a, Trans b,
           Typeable a,Typeable b) => Trans (a,b)
    where createComm = do   (cx,x) <- createC
                            (cy,y) <- createC
                            return (Comm (write2 (cx,cy)),(x,y))
instance (Trans a, Trans b, Trans c,
           Typeable a,Typeable b,Typeable c) => Trans (a,b,c)
    where createComm = do   (cx,x) <- createC
                            (cy,y) <- createC
                            (cz,z) <- createC
                            return (Comm (write3 (cx,cy,cz)),(x,y,z))
instance (Trans a, Trans b, Trans c, Trans d,
           Typeable a,Typeable b,Typeable c,Typeable d) => Trans (a,b,c,d)
    where createComm = do   (ca,a) <- createC
                            (cb,b) <- createC
                            (cc,c) <- createC
                            (cd,d) <- createC
                            return (Comm (write4 (ca,cb,cc,cd)),
                                (a,b,c,d))
instance (Trans a, Trans b, Trans c,  Trans d, Trans e,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e)
     => Trans (a,b,c,d,e)
    where createComm = do       (ca,a) <- createC
                                (cb,b) <- createC
                                (cc,c) <- createC
                                (cd,d) <- createC
                                (ce,e) <- createC
                                return (Comm (write5 (ca,cb,cc,cd,ce)),
                                    (a,b,c,d,e))
instance (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f)
     => Trans (a,b,c,d,e,f)
    where createComm = do   (ca,a) <- createC
                            (cb,b) <- createC
                            (cc,c) <- createC
                            (cd,d) <- createC
                            (ce,e) <- createC
                            (cf,f) <- createC
                            return (Comm (write6 (ca,cb,cc,cd,ce,cf)),
                                (a,b,c,d,e,f))
instance (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f, Trans g,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f,Typeable g)
     => Trans (a,b,c,d,e,f,g)
    where createComm = do   (ca,a) <- createC
                            (cb,b) <- createC
                            (cc,c) <- createC
                            (cd,d) <- createC
                            (ce,e) <- createC
                            (cf,f) <- createC
                            (cg,g) <- createC
                            return (Comm (write7 (ca,cb,cc,cd,ce,cf,cg)),
                                (a,b,c,d,e,f,g))

instance (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f, Trans g, Trans h,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f,Typeable g,Typeable h)
     => Trans (a,b,c,d,e,f,g,h)
    where createComm = do   (ca,a) <- createC
                            (cb,b) <- createC
                            (cc,c) <- createC
                            (cd,d) <- createC
                            (ce,e) <- createC
                            (cf,f) <- createC
                            (cg,g) <- createC
                            (ch,h) <- createC
                            return (Comm (write8 (ca,cb,cc,cd,ce,cf,cg,ch)),
                                (a,b,c,d,e,f,g,h))

instance (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f, Trans g, Trans h, Trans i,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f,Typeable g,Typeable h,Typeable i)
     => Trans (a,b,c,d,e,f,g,h,i)
    where createComm = do   (ca,a) <- createC
                            (cb,b) <- createC
                            (cc,c) <- createC
                            (cd,d) <- createC
                            (ce,e) <- createC
                            (cf,f) <- createC
                            (cg,g) <- createC
                            (ch,h) <- createC
                            (ci,i) <- createC
                            return (Comm (write9 (ca,cb,cc,cd,ce,cf,cg,ch,ci)),
                                (a,b,c,d,e,f,g,h,i))
-- bigger tuples use standard communication

------------------------------------------------------------------------------
-- helper functions for Trans class:

-- send function for a single data type (no tuple, non-concurrent)
sendVia :: (NFData a,
        Trans a, Typeable a)
       => (ChanName' a) -> a -> IO()
sendVia c d = connectToPort c >>
              (sendData Connect d) >> -- optional: connect before evaluation
              write d

---------------------------------------------------------
-- send functions for tuples...
write2 :: (Trans a, Trans b,
           Typeable a,Typeable b) => (ChanName' a, ChanName' b) -> (a,b) -> IO ()
write2 (c1,c2) (x1,x2) = do
        fork (sendVia c1 x1)
        sendVia c2 x2
write3 :: (Trans a, Trans b, Trans c,
           Typeable a,Typeable b,Typeable c)
        => (ChanName' a, ChanName' b, ChanName' c) -> (a,b,c) -> IO ()
write3 (c1,c2,c3) (x1,x2,x3) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        sendVia c3 x3
write4 :: (Trans a, Trans b, Trans c, Trans d,
           Typeable a,Typeable b,Typeable c,Typeable d)
        => (ChanName' a, ChanName' b, ChanName' c, ChanName' d
      ) -> (a,b,c,d) -> IO ()
write4 (c1,c2,c3,c4) (x1,x2,x3,x4) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        fork (sendVia c3 x3)
        sendVia c4 x4
write5 :: (Trans a, Trans b, Trans c, Trans d, Trans e,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e)
        => (ChanName' a, ChanName' b, ChanName' c, ChanName' d, ChanName' e
      ) -> (a,b,c,d,e) -> IO ()
write5 (c1,c2,c3,c4,c5) (x1,x2,x3,x4,x5) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        fork (sendVia c3 x3)
        fork (sendVia c4 x4)
        sendVia c5 x5
write6 :: (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f)
        => (ChanName' a, ChanName' b, ChanName' c, ChanName' d,
       ChanName' e, ChanName' f
      ) -> (a,b,c,d,e,f) -> IO ()
write6 (c1,c2,c3,c4,c5,c6) (x1,x2,x3,x4,x5,x6) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        fork (sendVia c3 x3)
        fork (sendVia c4 x4)
        fork (sendVia c5 x5)
        sendVia c6 x6
write7 :: (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f, Trans g,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f,Typeable g)
        => (ChanName' a, ChanName' b, ChanName' c, ChanName' d,
       ChanName' e, ChanName' f, ChanName' g
      ) -> (a,b,c,d,e,f,g) -> IO ()
write7 (c1,c2,c3,c4,c5,c6,c7) (x1,x2,x3,x4,x5,x6,x7) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        fork (sendVia c3 x3)
        fork (sendVia c4 x4)
        fork (sendVia c5 x5)
        fork (sendVia c6 x6)
        sendVia c7 x7
write8 :: (Trans a, Trans b, Trans c, Trans d, Trans e, Trans f, Trans g, Trans h,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f,Typeable g,Typeable h)
        => (ChanName' a, ChanName' b, ChanName' c, ChanName' d,
       ChanName' e, ChanName' f, ChanName' g, ChanName' h
      ) -> (a,b,c,d,e,f,g,h) -> IO ()
write8 (c1,c2,c3,c4,c5,c6,c7,c8) (x1,x2,x3,x4,x5,x6,x7,x8) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        fork (sendVia c3 x3)
        fork (sendVia c4 x4)
        fork (sendVia c5 x5)
        fork (sendVia c6 x6)
        fork (sendVia c7 x7)
        sendVia c8 x8
write9 :: (Trans a,Trans b,Trans c,Trans d,Trans e,Trans f,Trans g,Trans h,Trans i,
           Typeable a,Typeable b,Typeable c,Typeable d,Typeable e,Typeable f,Typeable g,Typeable h,Typeable i)
        => (ChanName' a, ChanName' b, ChanName' c, ChanName' d,
       ChanName' e, ChanName' f, ChanName' g, ChanName' h, ChanName' i
      ) -> (a,b,c,d,e,f,g,h,i) -> IO ()
write9 (c1,c2,c3,c4,c5,c6,c7,c8,c9) (x1,x2,x3,x4,x5,x6,x7,x8,x9) = do
        fork (sendVia c1 x1)
        fork (sendVia c2 x2)
        fork (sendVia c3 x3)
        fork (sendVia c4 x4)
        fork (sendVia c5 x5)
        fork (sendVia c6 x6)
        fork (sendVia c7 x7)
        fork (sendVia c8 x8)
        sendVia c9 x9
