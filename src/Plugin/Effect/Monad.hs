{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TupleSections             #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
module Plugin.Effect.Monad where

import Control.Exception
import Control.Monad.State
import Control.Monad.SearchTree
import Control.Monad.Codensity ( Codensity(..) )

import           Data.Map                       (Map)
import qualified Data.Map           as Map
import           Data.Set                       (Set)
import qualified Data.Set           as Set
import           Data.Maybe
import           Data.SBV
import           Data.SBV.Control

import           Test.ChasingBottoms.IsBottom

import           Unsafe.Coerce
import           System.IO.Unsafe

import Plugin.Effect.Tree

--------------------------------------------------------------------------------

data Untyped = forall a. Untyped a

type ID = Integer

type Heap = Map ID Untyped

insertBinding :: ID -> a -> Heap -> Heap
insertBinding i = Map.insert i . Untyped

findBinding :: ID -> Heap -> Maybe a
findBinding i = fmap (\ (Untyped x) -> unsafeCoerce x) . Map.lookup i

--------------------------------------------------------------------------------

type Constraint = SBool

type ConstraintStore = ([Constraint], Set ID)

insertConstraint :: Constraint -> [ID] -> ConstraintStore -> ConstraintStore
insertConstraint c ids (cs, vs) = (c:cs, Set.fromList ids `Set.union` vs)

isConsistent :: ConstraintStore -> Bool
isConsistent cst = unsafePerformIO $ runSMT $ do
  mapM_ constrain $ fst cst
  query $ checkSat >>= \case
    Sat -> return True
    _   -> return False

isUnconstrained :: ID -> ConstraintStore -> Bool
isUnconstrained i = Set.notMember i . snd

toSBV :: SymVal a => FLVal a -> SBV a
toSBV (Var i) = sym $ "x" ++ (if i < 0 then "n" else "") ++ show (abs i)
toSBV (Val a) = literal a

--------------------------------------------------------------------------------

type ND = Codensity (StateT (ID, Heap, ConstraintStore) Search)

evalND :: ND a -> [a]
evalND nd = bfs (evalStateT (runCodensity nd return) (0, mempty, mempty))

execND :: ND a -> [Heap]
execND nd = (\ (_, h, _) -> h) <$> bfs (execStateT (runCodensity nd return) (0, mempty, mempty))

--------------------------------------------------------------------------------

data PrimitiveInfo a = NoPrimitive
                     | SymVal a => Primitive

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a
  primitiveInfo = NoPrimitive

--------------------------------------------------------------------------------

data FLVal a = (Narrowable a, HasPrimitiveInfo a) => Var ID | Val { unVal :: a }

newtype FL a = FL { unFL :: ND (FLVal a) }

instance Functor FL where
  fmap = fmapFL

instance Applicative FL where
  pure = returnFL
  mf <*> mx = mf >>= \f -> mx >>= \x -> return (f x)

instance Monad FL where
  (>>=) = bindFL

returnFL :: a -> FL a
returnFL x = FL (return (Val x))

freeFL :: (Narrowable a, HasPrimitiveInfo a) => ID -> FL a
freeFL i = FL (return (Var i))

class Narrowable a where
  -- TODO: somehow we only want one ID, but have not figured out how to to that yet.
  -- Thus, for now the first is the variable to be narrowed and the second is the next fresh ID
  narrow :: ID -> ID -> ConstraintStore -> [(a, Integer)]
  default narrow :: (Bounded a, Enum a) => ID -> ID -> ConstraintStore -> [(a, Integer)]
  narrow _ _ _ = [(x, 0) | x <- [minBound .. maxBound]]

narrowPrimitive :: (SymVal a, Narrowable a, HasPrimitiveInfo a) => ID -> ID -> ConstraintStore -> [(a, Integer)]
narrowPrimitive i j cst = unsafePerformIO $ runSMT $ do
  mapM_ constrain $ fst cst
  query $ checkSat >>= \case
    Sat -> do
      v <- getValue (toSBV (Var i))
      let c = toSBV (Var i) ./== toSBV (Val v)
      return ((v, 0) : narrowPrimitive i j (insertConstraint c [i] cst))
    _   -> return []

instantiateND :: forall a. (Narrowable a, HasPrimitiveInfo a) => ID -> ND a
instantiateND i = lift get >>= \ (j, h, cst) -> case findBinding i h of
  Nothing -> msum (map update (narrow i j cst))
    where
      update (x, o) =
        let cst' = case primitiveInfo @a of
                      NoPrimitive -> cst
                      Primitive   ->
                        let c = toSBV (Var i) .=== toSBV (Val x)
                        in insertConstraint c [i] cst
        in lift (put (j + o, insertBinding i x h, cst')) >> return x
  Just x  -> return x

bindFL :: FL a -> (a -> FL b) -> FL b
bindFL (FL nd) f = FL $ nd >>= \case
  Var i -> instantiateND i >>= unFL . f
  Val x -> unFL (f x)

thenFL :: FL a -> FL b -> FL b
thenFL fl = bindFL fl . const

fmapFL :: (a -> b) -> FL a -> FL b
fmapFL f a = a `bindFL` \a' ->
  returnFL (f a')

failFL :: String -> FL a
failFL s = FL (fail s)

failedFL :: FL a
failedFL = FL mzero

class (Narrowable a, HasPrimitiveInfo a) => Groundable a where
  groundFL :: FL a -> FL a
  groundFL = (`bindFL` returnFL)

evalFL :: Groundable a => FL a -> [a]
evalFL = map unVal . evalND . unFL . groundFL

execFL :: FL a -> [Heap]
execFL = execND . unFL

--------------------------------------------------------------------------------

-- Unfortunately, this type family cannot be declared as injective in GHC (although it is).
type family Lifted (a :: k) :: k

type instance Lifted (f a) = (Lifted f) (Lifted a)

--------------------------------------------------------------------------------

class Convertible a where
  to :: a -> Lifted a
  default to :: (a ~ Lifted a) => a -> Lifted a
  to !x = x
  -- In contrast to the paper, we need the heap as an additional argument,
  -- because not every argument to 'from' is in ground normal form.
  -- This is the case for inverses used in functional patterns.
  from :: Heap -> Lifted a -> a
  default from :: (a ~ Lifted a) => Heap -> Lifted a -> a
  from _ !x = x

-- This function already incorporates the improvement from the paper for
-- partial values in the context of partial inversion with higher-order functions.
toFL :: Convertible a => a -> FL (Lifted a)
toFL x | isBottom x = failedFL
       | otherwise  = returnFL (to x)

data FreeVariableException = FreeVariableException

instance Show FreeVariableException where
  show FreeVariableException = "free variable occured"

instance Exception FreeVariableException

fromFL :: Convertible a => Heap -> FL (Lifted a) -> a
fromFL h (FL nd) = case head (evalND nd) of
  Var i -> retrieve i h
  Val x -> from h x

retrieve :: Convertible a => ID ->  Heap -> a
retrieve i h = from h (fromMaybe (throw FreeVariableException) (findBinding i h))

--------------------------------------------------------------------------------

class Matchable a where
  match :: a -> Lifted a -> FL ()
  default match :: (a ~ Lifted a, Eq a) => a -> Lifted a -> FL ()
  match x y = if x == y then returnFL () else failedFL

matchFL :: forall a. (Convertible a, Matchable a, HasPrimitiveInfo (Lifted a)) => a -> FL (Lifted a) -> FL ()
matchFL x (FL nd) = FL $ nd >>= \case
  Var i -> lift get >>= \ (j, h, cst) -> case findBinding i h of
    Nothing -> case primitiveInfo @(Lifted a) of
                  NoPrimitive -> update cst
                  Primitive   ->
                    let c    = toSBV (Var i) .=== toSBV (Val (to x))
                        cst' = insertConstraint c [i] cst
                    in if isUnconstrained i cst || isConsistent cst'
                      then update cst'
                      else unFL failedFL
      where
        update cst' = lift (put (j, insertBinding i (to x) h, cst')) >>
                      return (Val ())
    Just y  -> unFL $ match x y
  Val y -> unFL $ match x y

linMatchFL :: forall a. (Convertible a, Matchable a) => a -> FL (Lifted a) -> FL ()
linMatchFL x (FL nd) = FL $ nd >>= \case
  Var i -> lift get >>= \ (j, h, cst) -> do -- just do "update cst"
    lift (put (j, insertBinding i (to x) h, cst))
    return (Val ())
  Val y -> unFL $ match x y

--------------------------------------------------------------------------------

class (Matchable a, Convertible a, Groundable (Lifted a)) => Invertible a

--------------------------------------------------------------------------------

data (-->) a b where
  Func        :: (FL a -> FL b) -> (a --> b)
  HaskellFunc :: (Invertible c, Convertible d) => (c -> d) -> (Lifted c --> Lifted d)

infixr 0 -->

type instance Lifted (->) = (-->)

instance HasPrimitiveInfo (a --> b)

instance Narrowable (a --> b) where
  narrow _ = error "cannot narrow functions"

instance (Invertible a, Convertible b) => Convertible (a -> b) where
  to f = HaskellFunc f

  from _ (HaskellFunc f) = unsafeCoerce f
  from _ (Func        _) = error "Cannot convert function type"

appFL :: FL (a --> b) -> FL a -> FL b
mf `appFL` x = mf >>= \case
  Func f        -> f x
  HaskellFunc f -> groundFL x >>= (toFL . f . from mempty)
