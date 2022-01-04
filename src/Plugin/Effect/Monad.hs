{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module Plugin.Effect.Monad where

import Control.Exception
import Control.Applicative (Alternative(..))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.SearchTree
import Control.Monad.Codensity ( Codensity(..) )

import           Data.Map                       (Map)
import qualified Data.Map           as Map
import           Data.Set                       (Set)
import qualified Data.Set           as Set
import           Data.SBV
import           Data.SBV.Control
#ifdef TYPED
import           Data.Typeable (Typeable)
#endif
import           Test.ChasingBottoms.IsBottom (isBottom)
import           Data.Coerce
import           Unsafe.Coerce
import           System.IO.Unsafe

import           Plugin.Effect.Tree
import Data.Typeable

type ND s = Codensity (ReaderT s Search)

evalND :: ND s a -> s -> Search a
evalND nd = runReaderT (runCodensity nd return)

--------------------------------------------------------------------------------
#ifdef TYPED
data FLVal a = (Narrowable a, Typeable a, HasPrimitiveInfo a) => Var ID | Val a
#else
data FLVal a = (Narrowable a, HasPrimitiveInfo a) => Var ID | Val a
#endif

unVal :: FLVal a -> a
unVal (Val x) = x
unVal (Var _) = throw FreeVariableException
--------------------------------------------------------------------------------

newtype FL a = FL { unFL :: ND FLState (FLVal a) }

evalFL :: FL a -> Search a
evalFL (FL nd) = unVal <$> evalND nd initFLState

instance Functor FL where
  fmap = liftM

instance Applicative FL where
  pure x = FL (return (Val x))
  (<*>) = ap

instance Monad FL where
  (FL nd) >>= f = FL $
    nd >>= \case
      Var i -> instantiateND i >>= unFL . f
      Val x -> unFL (f x)

instance Alternative FL where
  empty = FL empty
  FL a1 <|> FL a2 = FL (a1 <|> a2)

instance MonadPlus FL

instance MonadFail FL where
  fail s = FL (fail s)

#ifdef TYPED
freeFL :: (Narrowable a, Typeable a, HasPrimitiveInfo a) => ID -> FL a
#else
freeFL :: (Narrowable a, HasPrimitiveInfo a) => ID -> FL a
#endif
freeFL i = FL (return (Var i))

--------------------------------------------------------------------------------

data FLState = FLState {
    nextID :: ID,
    heap   :: Heap,
    constraints :: [Constraint],
    constrainedVars :: Set ID
  }

initFLState :: FLState
initFLState = FLState {
    nextID = 0,
    heap = Map.empty,
    constraints = [],
    constrainedVars = Set.empty
  }

--------------------------------------------------------------------------------

#ifdef TYPED
data Untyped = forall a. Typeable a => Untyped a
#else
data Untyped = forall a. Untyped a
#endif

type ID = Integer

type Heap = Map ID Untyped

#ifdef TYPED
insertBinding :: Typeable a => ID -> a -> Heap -> Heap
#else
insertBinding :: ID -> a -> Heap -> Heap
#endif
insertBinding i = Map.insert i . Untyped

#ifdef TYPED
findBinding :: Typeable a => ID -> Heap -> Maybe a
findBinding i = fmap (\(Untyped x) -> undefined x) . Map.lookup i --TODO
#else
findBinding :: ID -> Heap -> Maybe a
findBinding i = fmap (\(Untyped x) -> unsafeCoerce x) . Map.lookup i
#endif

--------------------------------------------------------------------------------

type Constraint = SBool

type ConstraintStore = ([Constraint], Set ID)

insertConstraint :: Constraint -> [ID] -> ConstraintStore -> ConstraintStore
insertConstraint c ids (cs, vs) = (c : cs, Set.fromList ids `Set.union` vs)

isConsistent :: ConstraintStore -> Bool
isConsistent cst = unsafePerformIO $
  runSMT $ do
    mapM_ constrain $ fst cst
    query $
      checkSat >>= \case
        Sat -> return True
        _ -> return False

isUnconstrained :: ID -> ConstraintStore -> Bool
isUnconstrained i = Set.notMember i . snd

toSBV :: (Coercible a b, SymVal b) => FLVal a -> SBV b
toSBV (Var i) = sym $ "x" ++ (if i < 0 then "n" else "") ++ show (abs i)
toSBV (Val a) = literal (coerce a)

--------------------------------------------------------------------------------

data PrimitiveInfo a = NoPrimitive
                     | forall b. (Coercible a b, SymVal b) => Primitive (Proxy (a, b))

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a
  primitiveInfo = NoPrimitive

--------------------------------------------------------------------------------

class Narrowable a where
  -- TODO: somehow we only want one ID, but have not figured out how to to that yet.
  -- Thus, for now the first is the variable to be narrowed and the second is the next fresh ID
  narrow :: ID -> ID -> ConstraintStore -> [(a, Integer)]

narrowPrimitive :: forall a b. (HasPrimitiveInfo a, Narrowable a, Coercible a b, SymVal b) => ID -> ID -> ConstraintStore -> [(a, Integer)]
narrowPrimitive i j cst = unsafePerformIO $ runSMT $ do
  mapM_ constrain $ fst cst
  query $ checkSat >>= \case
    Sat -> do
      v <- coerce @b @a <$> getValue (toSBV @a @b (Var i))
      let c = toSBV @a @b (Var i) ./== toSBV (Val v)
      return ((v, 0) : narrowPrimitive @a @b i j (insertConstraint c [i] cst))
    _   -> return []

-- TODO: combine narrowable typeable and hasprimitiveinfo
#ifdef TYPED
instantiateND :: forall a. (Narrowable a, Typeable a, HasPrimitiveInfo a) => ID -> ND FLState a
#else
instantiateND :: forall a. (Narrowable a, HasPrimitiveInfo a) => ID -> ND FLState a
#endif
instantiateND i = get >>= \ FLState {..} -> case findBinding i heap of
  Nothing -> msum (map update (narrow i nextID (constraints, constrainedVars)))
    where
      update (x, o) =
        let cst' = case primitiveInfo of
                      NoPrimitive                     -> (constraints, constrainedVars)
                      Primitive (_ :: (Proxy (a, b))) ->
                        let c = toSBV @a @b (Var i) .=== toSBV @a @b (Val x)
                        in insertConstraint c [i] (constraints, constrainedVars)
        in put (FLState (nextID + o) (insertBinding i x heap) (fst cst') (snd cst')) >> return x
  Just x  -> return x

class (Narrowable a, HasPrimitiveInfo a) => NF a where
  nf :: (forall x. NF x => FL x -> FL x) -> a -> FL a
  nf _ = return

groundNormalFormFL :: NF a => FL a -> FL a
groundNormalFormFL x = x >>= nf groundNormalFormFL

normalFormFL :: NF a => FL a -> FL a
normalFormFL (FL nd) = FL $ nd >>= \case
  Val x -> unFL $ nf normalFormFL x
  Var i -> get >>= \FLState { .. } -> case findBinding i heap of
    Nothing -> return (Var i)
    Just x  -> unFL $ nf normalFormFL x

--------------------------------------------------------------------------------

-- Unfortunately, this type family cannot be declared as injective in GHC (although it is).
type family Lifted (m :: * -> *) (a :: k) = (b :: k) | b -> m a

--------------------------------------------------------------------------------

class Convertible a where
  to :: a -> Lifted FL a

  from :: Lifted FL a -> a

-- This function already incorporates the improvement from the paper for
-- partial values in the context of partial inversion with higher-order functions.
toFL :: Convertible a => a -> FL (Lifted FL a)
toFL x | isBottom x = empty
       | otherwise  = return (to x)

data FreeVariableException = FreeVariableException

instance Show FreeVariableException where
  show FreeVariableException = "free variable occured"

instance Exception FreeVariableException

fromFL :: Convertible a => FL (Lifted FL a) -> a
fromFL = from . head . bfs . evalFL

--------------------------------------------------------------------------------

class Matchable a where
  match :: a -> Lifted FL a -> FL ()

matchFL :: forall a. (Convertible a, Matchable a, HasPrimitiveInfo (Lifted FL a)) => a -> FL (Lifted FL a) -> FL ()
matchFL x (FL nd) = FL $ nd >>= \case
  Var i -> get >>= \ FLState { .. } -> case findBinding i heap of
    Nothing -> case primitiveInfo @(Lifted FL a) of
                  NoPrimitive                               -> update (constraints, constrainedVars)
                  Primitive (_ :: (Proxy (Lifted FL a, b))) ->
                    let c    = toSBV @(Lifted FL a) @b (Var i) .=== toSBV @(Lifted FL a) @b (Val (to x))
                        cst' = insertConstraint c [i] (constraints, constrainedVars)
                    in if isUnconstrained i (constraints, constrainedVars) || isConsistent (constraints, constrainedVars)
                      then update cst'
                      else unFL empty
      where
        update (cst, vs) = put (FLState nextID (insertBinding i (to x) heap) cst vs) >> return (Val ())
    Just y  -> unFL $ match x y
  Val y -> unFL $ match x y

-- linMatchFL :: forall a. (Convertible a, Matchable a) => a -> FL (Lifted a) -> FL ()
-- linMatchFL x (FL nd) = FL $ nd >>= \case
--   Var i -> lift get >>= \ (j, h, cst) -> do -- just do "update cst"
--     lift (put (j, insertBinding i (to x) h, cst))
--     return (Val ())
--   Val y -> unFL $ match x y

--------------------------------------------------------------------------------

class (Matchable a, Convertible a, NF (Lifted FL a)) => Invertible a

--------------------------------------------------------------------------------


infixr 0 :-->
type (:-->) = (-->) FL

data (-->) (m :: * -> *) (a :: *) (b :: *) where
  Func        :: (FL a -> FL b) -> (-->) m a b
  HaskellFunc :: (Invertible c, Convertible d) => (c -> d) -> (-->) m (Lifted FL c) (Lifted FL d)

infixr 0 -->

type instance Lifted m (->) = (-->) m
type instance Lifted m ((->) a) = (-->) m (Lifted m a)
type instance Lifted m ((->) a b) = (-->) m (Lifted m a) (Lifted m b)

instance (Invertible a, Convertible b) => Convertible (a -> b) where
  to f = HaskellFunc f

  from (HaskellFunc f) = unsafeCoerce f
  from (Func        _) = error "Cannot convert function type"

appFL :: FL ((-->) FL a b) -> FL a -> FL b
mf `appFL` x = mf >>= \case
  Func f        -> f x
  HaskellFunc f -> groundNormalFormFL x >>= (toFL . f . from)
