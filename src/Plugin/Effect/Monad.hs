{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UnboxedTuples             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# OPTIONS_GHC -Wno-orphans           #-}

module Plugin.Effect.Monad where

import Control.Exception
import Control.Applicative     (Alternative(..))
import Control.Monad.Codensity (Codensity(..))
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.SearchTree
import Control.Monad.State

import           Data.Either               (fromRight)
import qualified Data.Kind
import           Data.Map                  (Map)
import qualified Data.Map           as Map
import           Data.Set                  (Set)
import qualified Data.Set           as Set
import           Data.Typeable             (type (:~:)(..))
#ifdef TYPED
import           Data.Typeable             (Typeable)
#endif

import Plugin.Effect.SolverLibrary.SBV ()
import Plugin.Lifted

import Test.ChasingBottoms.IsBottom (isBottom)

import Unsafe.Coerce (unsafeCoerce)
{-
--TODO: for testing only
import Data.Coerce
import Plugin.BuiltIn.Primitive
import Plugin.Effect.Tree-}

--------------------------------------------------------------------------------

type ND s = Codensity (ReaderT s Search)

evalND :: ND s a -> s -> Search a
evalND nd = runReaderT (runCodensity nd return)

--------------------------------------------------------------------------------

type ID = Integer

--------------------------------------------------------------------------------

#ifdef TYPED
data Untyped = forall a. Typeable a => Untyped a
#else
data Untyped = forall a. Untyped a
#endif

type Heap = Map ID Untyped

emptyHeap :: Heap
emptyHeap = Map.empty

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

class Narrowable a where
  narrow :: ID -> [(a, Integer)]

--------------------------------------------------------------------------------

--TODO: Remark on redundancy (other word): although many constraints could be expressed using other constraints, we have all possible functions in our interface in order for libraries to be able to invoke the natively supported operation instead of imitating (other word) it...
class SolverLibrary where
  type Constraint

  checkConsistency :: [Constraint] -> Bool

  type Constrainable a :: Data.Kind.Constraint

  getModels :: Constrainable a => ID -> [Constraint] -> [a]

  eqConstraint :: Constrainable a => FLVal a -> FLVal a -> Constraint
  notConstraint :: Constraint -> Constraint --TODO: necessary? Schon praktischer, weil wir dann nicht das gegenteil haben müssen.
  neqConstraint :: Constrainable a => FLVal a -> FLVal a -> Constraint
  neqConstraint x y = notConstraint (eqConstraint x y)
  --TODO: das hier ist eigentlich definitiv nicht notwendig, da man es mit negate und eqConstraint bekommt. einige implementierungen wie sbv unterstützen es aber direkt. what4 bspw. nicht. in jedem fall wird es aber von jeder implementierung unterstützt und sollte daher nicht maybe sein.

  intPlusConstraint, intMinusConstraint, intMulConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)
  integerPlusConstraint, integerMinusConstraint, integerMulConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)
  floatPlusConstraint, floatMinusConstraint, floatMulConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)
  doublePlusConstraint, doubleMinusConstraint, doubleMulConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  intLtConstraint, intLeqConstraint, intGtConstraint, intGeqConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)
  integerLtConstraint, integerLeqConstraint, integerGtConstraint, integerGeqConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)
  floatLtConstraint, floatLeqConstraint, floatGtConstraint, floatGeqConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)
  doubleLtConstraint, doubleLeqConstraint, doubleGtConstraint, doubleGeqConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)
  charLtConstraint, charLeqConstraint, charGtConstraint, charGeqConstraint :: Maybe (FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> Constraint)
  --TODO: in datentypen für typklassen zusammenfassen? DAnn kann man die parametrisieren...

--------------------------------------------------------------------------------

data ConstraintStore = ConstraintStore {
    constraints     :: [Constraint],
    --TODO: The most commonly executed action will be the insertion of a constraint. Therefore we use a list for which the insertion is done in constant time. As for the lookup action: Everytime we need to check for consistency, we have to visit each constraint anyway.
    constrainedVars :: Set ID
    --TODO: Consistency checks are very time-consuming: Each time we have to call the external SMT solver and go through its entire cycle. In order to be able to minimize the frequency of consistency checks, we record the set of constrained variables. This way we can avoid a new consistency check when a variable is constrained that has not been recorded before.
  }

initConstraintStore :: ConstraintStore
initConstraintStore = ConstraintStore {
    constraints     = [],
    constrainedVars = Set.empty
  }

--TODO: [ID] parameter only for efficiency reason
insertConstraint :: Constraint -> [ID] -> ConstraintStore -> ConstraintStore
insertConstraint c ids ConstraintStore { .. } =
  ConstraintStore { constraints = c : constraints, constrainedVars = Set.fromList ids `Set.union` constrainedVars }

isUnconstrained :: ID -> ConstraintStore -> Bool
isUnconstrained i = Set.notMember i . constrainedVars

isConsistent :: ConstraintStore -> Bool
isConsistent = checkConsistency . constraints

generate :: Constrainable a => ID -> ConstraintStore -> [a]
generate i = getModels i . constraints

--------------------------------------------------------------------------------

data PrimitiveInfo a = Narrowable a => NoPrimitive
                     | Constrainable a => Primitive

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a

--------------------------------------------------------------------------------

#ifdef TYPED
data FLVal a = (HasPrimitiveInfo a, Typeable a) => Var ID | Val a
#else
data FLVal a = HasPrimitiveInfo a => Var ID | Val a
#endif

--------------------------------------------------------------------------------

data FLState = FLState {
    nextID          :: ID,
    heap            :: Heap,
    constraintStore :: ConstraintStore
  }

initFLState :: FLState
initFLState = FLState {
    nextID          = 0,
    heap            = emptyHeap,
    constraintStore = initConstraintStore
  }

--------------------------------------------------------------------------------

newtype FL a = FL { unFL :: ND FLState (FLVal a) }

instance Functor FL where
  fmap = liftM

instance Applicative FL where
  pure x = FL (pure (Val x))
  (<*>) = ap

resolve :: FL a -> ND FLState (FLVal a)
resolve fl = unFL fl >>= \case
  Val x -> return (Val x)
  Var i -> get >>= \ FLState { .. } -> case findBinding i heap of
    Nothing -> return (Var i)
    Just x  -> return (Val x)

#ifdef TYPED
instantiate :: forall a. (HasPrimitiveInfo a, Typeable a) => ID -> ND FLState a
#else
instantiate :: forall a. HasPrimitiveInfo a => ID -> ND FLState a
#endif
instantiate i = get >>= \ FLState { .. } ->
  case primitiveInfo @a of
    NoPrimitive -> msum (map update (narrow nextID))
      where update (x, o) = do
              put (FLState { nextID = nextID + o, heap = insertBinding i x heap, .. })
              return x
    Primitive   -> msum (map update (generate i constraintStore))
      where update x = do
              let c = eqConstraint (Var i) (Val x)
              put (FLState { heap =  insertBinding i x heap, constraintStore = insertConstraint c [i] constraintStore, .. })
              return x
instance Monad FL where
  fl >>= f = FL $
    resolve fl >>= \case
      Var i -> instantiate i >>= unFL . f
      Val x -> unFL (f x)

instance Alternative FL where
  empty = FL empty
  FL a1 <|> FL a2 = FL (a1 <|> a2)

instance MonadPlus FL

instance MonadFail FL where
  fail s = FL (fail s)

#ifdef TYPED
free :: (HasPrimitiveInfo a, Typeable a) => ID -> FL a
#else
free :: HasPrimitiveInfo a => ID -> FL a
#endif
free i = FL (return (Var i))

--------------------------------------------------------------------------------

class b ~ Lifted FL a => NormalForm a b | a -> b, b -> a where
  normalFormWith :: Applicative m => (forall c. NormalForm c (Lifted FL c) => FL (Lifted FL c) -> ND FLState (m (Lifted m c))) -> b -> ND FLState (m (Lifted m a))

--TODO: groundNormalFormND or groundNormalForm?
groundNormalFormFL :: NormalForm a (Lifted FL a) => FL (Lifted FL a) -> ND FLState (Identity (Lifted Identity a))
groundNormalFormFL fl = resolve fl >>= \case
  Val x -> normalFormWith groundNormalFormFL x
  Var i -> instantiate i >>= normalFormWith groundNormalFormFL

normalFormFL :: NormalForm a (Lifted FL a) => FL (Lifted FL a) -> ND FLState (Either ID (Lifted (Either ID) a))
normalFormFL fl = resolve fl >>= \case
  Val x -> normalFormWith normalFormFL x
  Var i -> return (Left i)

evalWith :: NormalForm a (Lifted FL a) => (forall b. NormalForm b (Lifted FL b) => FL (Lifted FL b) -> ND FLState (m (Lifted m b))) -> FL (Lifted FL a) -> Search (m (Lifted m a))
evalWith nf fl = evalND (nf fl) initFLState

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

--------------------------------------------------------------------------------

class Matchable a where
  match :: a -> Lifted FL a -> FL ()

--TODO: rename matchFL to something without FL?
matchFL :: forall a. (Convertible a, Matchable a) => a -> FL (Lifted FL a) -> FL ()
matchFL x fl = FL $ resolve fl >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { heap = insertBinding i (to x) heap, .. })
        return (Val ())
      Primitive   ->
        let c = eqConstraint (Var i) (Val (to x))
            constraintStore' = insertConstraint c [i] constraintStore
        in if isUnconstrained i constraintStore || isConsistent constraintStore'
          then do
            put (FLState { heap = insertBinding i (to x) heap, constraintStore = constraintStore', .. })
            return (Val ())
          else empty
  Val y  -> unFL $ match x y
  --TODO: Prettify?

-- linMatchFL :: forall a. (Convertible a, Matchable a) => a -> FL (Lifted a) -> FL ()
-- linMatchFL x (FL nd) = FL $ nd >>= \case
--   Var i -> lift get >>= \ (j, h, cst) -> do -- just do "update cst"
--     lift (put (j, insertBinding i (to x) h, cst))
--     return (Val ())
--   Val y -> unFL $ match x y

--------------------------------------------------------------------------------

class (Matchable a, Convertible a, NormalForm a (Lifted FL a), HasPrimitiveInfo (Lifted FL a)) => Invertible a

--------------------------------------------------------------------------------

--TODO: move?
infixr 0 :-->
type (:-->) = (-->) FL

data (-->) (m :: * -> *) (a :: *) (b :: *) where
  Func        :: (m a -> m b) -> (-->) m a b
  HaskellFunc :: (Convertible c, NormalForm c (Lifted FL c), Convertible d) => (c -> d) -> (-->) FL (Lifted FL c) (Lifted FL d)

infixr 0 -->

type instance Lifted m (->) = (-->) m
type instance Lifted m ((->) a) = (-->) m (Lifted m a)
type instance Lifted m ((->) a b) = (-->) m (Lifted m a) (Lifted m b)

-- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
-- Thus, we create the proof manually using unsafeCoerce
decomposeInjectivity :: Lifted m a ~ Lifted m b => a :~: b
decomposeInjectivity = unsafeCoerce Refl

instance (Convertible a, NormalForm a (Lifted FL a), Convertible b) => Convertible (a -> b) where
  to f = HaskellFunc f

  -- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
  -- from (HaskellFunc f) = unsafeCoerce f
  fromWith _ (HaskellFunc (f :: c -> d)) x = case (# decomposeInjectivity @FL @a @c, decomposeInjectivity @FL @b @d #) of
      (# Refl, Refl #) -> f x
  fromWith _ (Func        _) _ = error "Cannot convert function type"

appFL :: FL ((-->) FL a b) -> FL a -> FL b
mf `appFL` x = mf >>= \case
  Func f        -> f x
  HaskellFunc f -> FL $ groundNormalFormFL x >>= (unFL . toFL . f . fromIdentity)
{-

--TODO: For testing only

gFL :: FL (Lifted FL (Char -> Bool))
gFL = return $ Func $ \_ -> return TrueM

gInv :: Bool -> [Char]
gInv arg = map fromIdentity $ bfs $ evalWith groundNormalFormFL $ do
  matchFL arg (gFL `appFL` free (-1))
  free (-1)
instance HasPrimitiveInfo (CharFL FL) where
  primitiveInfo = Primitive

instance NormalForm Char (CharFL FL) where
  normalFormWith _ x = return (pure (coerce x))

instance Convertible Char where
  to = coerce

  fromWith _ = coerce

instance Matchable Char where
  match i1 i2 = guard (i1 == coerce i2)

instance Invertible Char

data BoolM (m :: * -> *) = FalseM | TrueM

type instance Lifted m Bool = BoolM m

instance Narrowable (BoolM FL) where
  narrow _ = [(FalseM, 0), (TrueM, 0)]

instance HasPrimitiveInfo (BoolM FL) where
  primitiveInfo = NoPrimitive

instance NormalForm Bool (BoolM FL) where
  normalFormWith _ = \case
    FalseM -> return (pure FalseM)
    TrueM  -> return (pure TrueM)

instance Convertible Bool where
  to False = FalseM
  to True  = TrueM

  fromWith _ FalseM = False
  fromWith _ TrueM  = True

instance Matchable Bool where
  match False FalseM = return ()
  match True  TrueM  = return ()
  match _     _      = empty

instance Invertible Bool-}