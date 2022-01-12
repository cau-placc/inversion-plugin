{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UnboxedTuples             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# OPTIONS_GHC -Wno-orphans           #-}
module Plugin.Effect.Monad where

import Control.Exception
import Control.Applicative (Alternative(..))
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.SearchTree
import Control.Monad.Codensity ( Codensity(..) )
import Control.Monad.Identity

import           Data.Map                       (Map)
import qualified Data.Map           as Map
import           Data.Set                       (Set)
import qualified Data.Set           as Set
import           Data.SBV
import           Data.SBV.Control
import           Data.SBV.Internals
#ifdef TYPED
import           Data.Typeable (Typeable)
#endif
import           Data.Either (fromRight)
import           Data.Coerce (coerce, Coercible )
import           Data.Typeable (type (:~:)(..))
import           Unsafe.Coerce (unsafeCoerce )
import           System.IO.Unsafe (unsafePerformIO)
import           Test.ChasingBottoms.IsBottom (isBottom)

type ND s = Codensity (ReaderT s Search)

evalND :: ND s a -> s -> Search a
evalND nd = runReaderT (runCodensity nd return)

--------------------------------------------------------------------------------
#ifdef TYPED
data FLVal a = (Narrowable a, Typeable a) => Var ID | Val a
#else
data FLVal a = Narrowable a => Var ID | Val a
#endif

--------------------------------------------------------------------------------

newtype FL a = FL { unFL :: ND FLState (FLVal a) }

evalWith :: NF a (Lifted FL a) => (forall b. NF b (Lifted FL b) => FL (Lifted FL b) -> ND FLState (m (Lifted m b))) -> FL (Lifted FL a) -> Search (m (Lifted m a))
evalWith nf fl = evalND (nf fl) initFLState

instance Functor FL where
  fmap = liftM

instance Applicative FL where
  pure x = FL (return (Val x))
  (<*>) = ap

instance Monad FL where
  (FL nd) >>= f = FL $
    nd >>= resolveND >>= \case
      Var i -> instantiateND i >>= unFL . f
      Val x -> unFL (f x)

instance Alternative FL where
  empty = FL empty
  FL a1 <|> FL a2 = FL (a1 <|> a2)

instance MonadPlus FL

instance MonadFail FL where
  fail s = FL (fail s)

#ifdef TYPED
freeFL :: (Narrowable a, Typeable a) => ID -> FL a
#else
freeFL :: Narrowable a => ID -> FL a
#endif
freeFL i = FL (return (Var i))

--------------------------------------------------------------------------------

data FLState = FLState {
    nextID          :: ID,
    heap            :: Heap,
    constraintStore :: ConstraintStore
  }

data ConstraintStore = CStore {
    constraints     :: [Constraint],
    constrainedVars :: Set ID
  }

initFLState :: FLState
initFLState = FLState {
    nextID = 0,
    heap = Map.empty,
    constraintStore = CStore {
      constraints = [],
      constrainedVars = Set.empty
    }
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
type Constrainable a = (Coercible (Lifted FL a) a, SymVal a)

instance SymVal Int where
  mkSymVal = genMkSymVar (KBounded True (finiteBitSize @Int 0))
  literal  = genLiteral  (KBounded True (finiteBitSize @Int 0))
  fromCV   = genFromCV

instance HasKind Int where
  kindOf _ = KBounded True (finiteBitSize @Int 0)

instance SDivisible (SBV Int) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

insertConstraint :: Constraint -> [ID] -> ConstraintStore -> ConstraintStore
insertConstraint c ids (CStore cs vs) = CStore (c : cs) (Set.fromList ids `Set.union` vs)

isConsistent :: ConstraintStore -> Bool
isConsistent cst = unsafePerformIO $
  runSMT $ do
    mapM_ constrain (constraints cst)
    query $ checkSat >>= \case
      Sat -> return True
      _ -> return False

isUnconstrained :: ID -> ConstraintStore -> Bool
isUnconstrained i = Set.notMember i . constrainedVars

toSBV :: Constrainable a => FLVal (Lifted FL a) -> SBV a
toSBV (Var i) = eitherToSBV (Left i)
toSBV (Val a) = eitherToSBV (Right a)

eitherToSBV :: Constrainable a => Either ID (Lifted FL a) -> SBV a
eitherToSBV (Left i) = sym $ "x" ++ (if i < 0 then "n" else "") ++ show (abs i)
eitherToSBV (Right x) = literal (coerce x)

varToSBV :: Constrainable a => ID -> SBV a
varToSBV i = eitherToSBV (Left i)

--------------------------------------------------------------------------------

data PrimitiveInfo a = NoPrimitive
                     | Constrainable a => Primitive

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a
  primitiveInfo = NoPrimitive

--------------------------------------------------------------------------------

class Narrowable a where
  -- TODO: somehow we only want one ID, but have not figured out how to to that yet.
  -- Thus, for now the first is the variable to be narrowed and the second is the next fresh ID
  narrow :: ID -> ID -> ConstraintStore -> [(a, Either Integer Constraint)]

-- TODO: remove j in diss
narrowPrimitive :: forall a. Constrainable a => ID -> ID -> ConstraintStore -> [(Lifted FL a, Either Integer Constraint)]
narrowPrimitive i j cst = unsafePerformIO $
  runSMT $ do
    mapM_ constrain (constraints cst)
    query $ checkSat >>= \case
      Sat -> do
        v <- getValue (eitherToSBV @a (Left i))
        let c = eitherToSBV (Left i) ./== literal v
        return ((coerce v, Right (sNot c)) : narrowPrimitive i j (insertConstraint c [i] cst))
      _   -> return []

--TODO: rename
resolveND :: FLVal a -> ND FLState (FLVal a)
resolveND (Val x) = return (Val x)
resolveND (Var i) = get >>= \ FLState {..} -> case findBinding i heap of
  Nothing -> return (Var i)
  Just x  -> return (Val x)

--TODO: nd >>= resolveND is very common

-- TODO: combine narrowable typeable and hasprimitiveinfo
#ifdef TYPED
instantiateND :: forall a. (Narrowable a, Typeable a) => ID -> ND FLState a
#else
instantiateND :: forall a. Narrowable a => ID -> ND FLState a
#endif
instantiateND i = get >>= \ FLState {..} ->
    let
      update (x, Left  o) = put (FLState (nextID + o) (insertBinding i x heap) constraintStore) >> return x
      update (x, Right c) = put (FLState nextID (insertBinding i x heap) (insertConstraint c [i] constraintStore)) >> return x
    in msum (map update (narrow i nextID constraintStore))

class (b ~ Lifted FL a, Narrowable b) => NF a b | a -> b, b -> a where
  normalFormWith :: Applicative m => (forall c. NF c (Lifted FL c) => FL (Lifted FL c) -> ND FLState (m (Lifted m c))) -> b -> ND FLState (m (Lifted m a))

groundNormalFormFL :: NF a (Lifted FL a) => FL (Lifted FL a) -> ND FLState (Identity (Lifted Identity a))
groundNormalFormFL (FL nd) = nd >>= resolveND >>= \case
  Val x -> normalFormWith groundNormalFormFL x
  Var i -> instantiateND i >>= normalFormWith groundNormalFormFL

normalFormFL :: NF a (Lifted FL a) => FL (Lifted FL a) -> ND FLState (Either ID (Lifted (Either ID) a))
normalFormFL (FL nd) = nd >>= resolveND >>= \case
  Val x -> normalFormWith normalFormFL x
  Var i -> return (Left i)

--------------------------------------------------------------------------------

-- Unfortunately, this type family cannot be declared as injective in GHC (although it is).
type family Lifted (m :: * -> *) (a :: k) = (b :: k) | b -> m a

--------------------------------------------------------------------------------

class Convertible a where
  to :: a -> Lifted FL a

  fromWith :: (forall b. Convertible b => m (Lifted m b) -> b) -> Lifted m a -> a

-- This function already incorporates the improvement from the paper for
-- partial values in the context of partial inversion with higher-order functions.
toFL :: Convertible a => a -> FL (Lifted FL a)
toFL x | isBottom x = empty
       | otherwise  = return (to x)

fromM :: Convertible a => (forall b. m b -> b) -> m (Lifted m a) -> a
fromM unM = fromWith (fromM unM) . unM

fromIdentity :: Convertible a => Identity (Lifted Identity a) -> a
fromIdentity = fromM runIdentity

data FreeVariableException = FreeVariableException

instance Show FreeVariableException where
  show FreeVariableException = "free variable occured"

instance Exception FreeVariableException

fromEither :: Convertible a => Either ID (Lifted (Either ID) a) -> a
fromEither = fromM (fromRight (throw FreeVariableException))

unsafeFrom :: Convertible a => Lifted FL a -> a
unsafeFrom = fromWith (error "Used 'unsafeFrom' on non-primitive value")

--------------------------------------------------------------------------------

class Matchable a where
  match :: a -> Lifted FL a -> FL ()

matchFL :: forall a. (Convertible a, Matchable a, HasPrimitiveInfo a) => a -> FL (Lifted FL a) -> FL ()
matchFL x (FL nd) = FL $ nd >>= resolveND >>= \case
  Var i -> get >>= \ FLState { .. } ->
    let update cst = put (FLState nextID (insertBinding i (to x) heap) cst) >> return (Val ())
    in case primitiveInfo @a of
        NoPrimitive -> update constraintStore
        Primitive   ->
          let c    = toSBV (Var i) .=== toSBV (Val (to x))
              cst' = insertConstraint c [i] constraintStore
          in if isUnconstrained i constraintStore || isConsistent cst'
            then update cst'
            else unFL empty
  Val y  -> unFL $ match x y

-- linMatchFL :: forall a. (Convertible a, Matchable a) => a -> FL (Lifted a) -> FL ()
-- linMatchFL x (FL nd) = FL $ nd >>= \case
--   Var i -> lift get >>= \ (j, h, cst) -> do -- just do "update cst"
--     lift (put (j, insertBinding i (to x) h, cst))
--     return (Val ())
--   Val y -> unFL $ match x y

--------------------------------------------------------------------------------

class (Matchable a, Convertible a, NF a (Lifted FL a), HasPrimitiveInfo a) => Invertible a

--------------------------------------------------------------------------------


infixr 0 :-->
type (:-->) = (-->) FL

data (-->) (m :: * -> *) (a :: *) (b :: *) where
  Func        :: (m a -> m b) -> (-->) m a b
  HaskellFunc :: (Convertible c, NF c (Lifted FL c), Convertible d) => (c -> d) -> (-->) FL (Lifted FL c) (Lifted FL d)

infixr 0 -->

type instance Lifted m (->) = (-->) m
type instance Lifted m ((->) a) = (-->) m (Lifted m a)
type instance Lifted m ((->) a b) = (-->) m (Lifted m a) (Lifted m b)

-- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
-- Thus, we create the proof manually using unsafeCoerce
decomposeInjectivity :: Lifted m a ~ Lifted m b => a :~: b
decomposeInjectivity = unsafeCoerce Refl

instance (Convertible a, NF a (Lifted FL a), Convertible b) => Convertible (a -> b) where
  to f = HaskellFunc f

  -- from (HaskellFunc f) = unsafeCoerce f -- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
  fromWith _ (HaskellFunc (f :: c -> d)) x = case (# decomposeInjectivity @FL @a @c, decomposeInjectivity @FL @b @d #) of
      (# Refl, Refl #) -> f x
  fromWith _ (Func        _) _ = error "Cannot convert function type"

appFL :: FL ((-->) FL a b) -> FL a -> FL b
mf `appFL` x = mf >>= \case
  Func f        -> f x
  HaskellFunc f -> FL $ groundNormalFormFL x >>= (unFL . toFL . f . fromIdentity)
