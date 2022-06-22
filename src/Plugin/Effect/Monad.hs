{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Plugin.Effect.Monad where

import Control.Exception
import Control.Applicative     (Alternative(..))
import Control.Monad.Codensity (Codensity(..))
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.SearchTree
import Control.Monad.State

import           Data.Kind                 (Type)
import qualified Data.Kind
import           Data.Map                  (Map)
import qualified Data.Map           as Map
import           Data.Set                  (Set)
import qualified Data.Set           as Set
import           Data.Typeable             (type (:~:)(..))

#ifdef USE_SBV
import Plugin.Effect.SolverLibrary.SBV   ()
#else
import Plugin.Effect.SolverLibrary.What4 ()
#endif
import Plugin.Effect.Tree
import Plugin.Lifted

import System.IO.Unsafe (unsafePerformIO)

import Test.ChasingBottoms.IsBottom (isBottom)

import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

class Monad m => MonadShare m where
  share :: Shareable m a => m a -> m (m a)

 -- adding MonadShare here as a context leads to a bug in the plugin when a quantified constraint ocurrs.
class Shareable m a where
  shareArgs :: a -> m a

--------------------------------------------------------------------------------

type ND s = Codensity (ReaderT s Search)

evalND :: ND s a -> s -> [a]
evalND nd = search . runReaderT (runCodensity nd return)
  where
#ifdef DEPTH_FIRST
    search = dfs
#elif defined(PARALLEL)
    search = ps
#else
    search = bfs
#endif

{-type ND1 s a = StateT s SearchTree a

evalND1 :: ND1 s a -> s -> SearchTree a
evalND1 = evalStateT

type ND2 s a = Codensity (ReaderT s SearchTree) a

evalND2 :: ND2 s a -> s -> SearchTree a
evalND2 nd = runReaderT (runCodensity nd return)

type ND3 s a = Codensity (ReaderT s (Codensity SearchTree)) a

evalND3 :: ND3 s a -> s -> SearchTree a
evalND3 nd s = runCodensity (runReaderT (runCodensity nd return) s) return-}

--------------------------------------------------------------------------------

type ID = Int --TODO: Enum voraussetzen, damit man mit pred den vrogänger berechnen kann. Id muss als schlüssel für den Heap verwendet werden können (d.h. im normalfall mindestens eq), integer ist ein guter wert, in der praxis

--------------------------------------------------------------------------------

type Heap a = Map ID a --TODO: intmap oder gar intmap von maja r.

emptyHeap :: Heap a
emptyHeap = Map.empty

insertHeap :: ID -> a -> Heap a -> Heap a
insertHeap = Map.insert

lookupHeap :: ID -> Heap a -> Maybe a
lookupHeap = Map.lookup

--------------------------------------------------------------------------------

data Untyped = forall a. Untyped a

typed :: Untyped -> a
typed (Untyped x) = unsafeCoerce x

insertBinding :: ID -> a -> Heap Untyped -> Heap Untyped
insertBinding i = insertHeap i . Untyped

findBinding :: ID -> Heap Untyped -> Maybe a
findBinding i = fmap typed . lookupHeap i

--------------------------------------------------------------------------------

class Narrowable a where
  narrow :: [a]
  --TODO: narrowSameConstr :: a -> a

--------------------------------------------------------------------------------

--TODO: Remark on redundancy (other word): although many constraints could be expressed using other constraints, we have all possible functions in our interface in order for libraries to be able to invoke the natively supported operation instead of imitating (other word) it...
class SolverLibrary where
  type Constraint

  checkConsistency :: [Constraint] -> Bool

  type Constrainable a :: Data.Kind.Constraint

  getModels :: Constrainable a => ID -> [Constraint] -> [a]

  eqConstraint :: Constrainable a => FLVal a -> FLVal a -> Constraint
  notConstraint :: Constraint -> Constraint
  neqConstraint :: Constrainable a => FLVal a -> FLVal a -> Constraint
  neqConstraint x y = notConstraint (eqConstraint x y)
  --TODO: das hier ist eigentlich definitiv nicht notwendig, da man es mit negate und eqConstraint bekommt. einige implementierungen wie sbv unterstützen es aber direkt. what4 bspw. nicht. in jedem fall wird es aber von jeder implementierung unterstützt und sollte daher nicht maybe sein.

  intPlusConstraint, intMinusConstraint, intMulConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)
  intNegateConstraint, intAbsConstraint, intSignumConstraint:: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)

  intQuotConstraint, intRemConstraint, intDivConstraint, intModConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)

  integerPlusConstraint, integerMinusConstraint, integerMulConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)
  integerNegateConstraint, integerAbsConstraint, integerSignumConstraint:: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)

  integerQuotConstraint, integerRemConstraint, integerDivConstraint, integerModConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)

  floatPlusConstraint, floatMinusConstraint, floatMulConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)
  floatNegateConstraint, floatAbsConstraint, floatSignumConstraint:: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)

  floatDivConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)

  doublePlusConstraint, doubleMinusConstraint, doubleMulConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)
  doubleNegateConstraint, doubleAbsConstraint, doubleSignumConstraint:: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  doubleDivConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  intLtConstraint, intLeqConstraint, intGtConstraint, intGeqConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)
  intMaxConstraint, intMinConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)

  integerLtConstraint, integerLeqConstraint, integerGtConstraint, integerGeqConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)
  integerMaxConstraint, integerMinConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)

  floatLtConstraint, floatLeqConstraint, floatGtConstraint, floatGeqConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)
  floatMaxConstraint, floatMinConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)

  doubleLtConstraint, doubleLeqConstraint, doubleGtConstraint, doubleGeqConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)
  doubleMaxConstraint, doubleMinConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  charLtConstraint, charLeqConstraint, charGtConstraint, charGeqConstraint :: Maybe (FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> Constraint)
  charMaxConstraint, charMinConstraint :: Maybe (FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> Constraint)

--------------------------------------------------------------------------------
data ConstraintStore = ConstraintStore {
    constraints     :: [Constraint],
    --TODO: The most commonly executed action will be the insertion of a constraint. Therefore we use a list for which the insertion is done in constant time. As for the lookup action: Everytime we need to check for consistency, we have to visit each constraint anyway.
    constrainedVars :: Set ID
    --TODO: Consistency checks are very time-consuming: Each time we have to call the external SMT solver and go through its entire cycle. In order to be able to minimize the frequency of consistency checks, we record the set of constrained variables. This way we can avoid a new consistency check when a variable is constrained that has not been recorded before.
  }

--TODO: Combinatorial explosion -> constraintstore erforderlich. sonst würde bei x == 0 instanziiert werden müssen und ganz viele bäume erzeugt werden.

-- TODO: type miniterium hacken, weltherrschft an mich reissen

initConstraintStore :: ConstraintStore
initConstraintStore = ConstraintStore {
    constraints     = [],
    constrainedVars = Set.empty
  }

--TODO: [ID] parameter only for efficiency reason
--TODO: no longer true as we need to know which variables are constrained in normal form computation. however, this could be possible by traversing all constrains everytime.
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

data PrimitiveInfo a = (Narrowable a, Shareable FL a) => NoPrimitive
                     | Constrainable a => Primitive

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a

--------------------------------------------------------------------------------

--data FLVal a = HasPrimitiveInfo a => Var ID | Val a
data FLVal (a :: Type) where
  Var        :: HasPrimitiveInfo a => ID -> FLVal a
  Val        :: a -> FLVal a
  HaskellVal :: To b => b -> FLVal (Lifted FL b)

  --TODO: stark ähnlich zu uneval von den set functions. nur war da die idee, dass der wert nicht umgewandelt werden muss, sondern der effekt da einfach unausgewertet drin stecken kann. bei der normalform berechnung müsste man einen weg haben, diesen wert nicht weiter anzuschauen

--------------------------------------------------------------------------------

data FLState = FLState {
    nextID          :: ID,
    heap            :: Heap Untyped,
    constraintStore :: ConstraintStore
  }
--TODO: getrennter heap?

initFLState :: FLState
initFLState = FLState {
    nextID          = -1,
    heap            = emptyHeap,
    constraintStore = initConstraintStore
  }

freshID :: ND FLState ID
freshID = do
  FLState { .. } <- get
  put (FLState { nextID = nextID - 1, .. })
  return nextID

--------------------------------------------------------------------------------

newtype FL a = FL { unFL :: ND FLState (FLVal a) }

instance Functor FL where
  fmap = liftM

instance Applicative FL where
  pure x = FL (pure (Val x))
  (<*>) = ap

--TODO: ketten durchbrechen und variable zurückliefern (instanziierung hängt von groundNF oder NF ab)
{-resolve :: FL a -> ND FLState (FLVal a)
resolve fl = unFL fl >>= \case
  Val x -> return (Val x)
  Var i -> get >>= \ FLState { .. } -> case findBinding i heap of
    Nothing -> return (Var i)
    Just x  -> resolve x-}

--TODO: name dereferenceFL
resolveFL :: FL a -> ND FLState (FLVal a)
resolveFL = resolveFL' []
  where resolveFL' is fl = unFL fl >>= \case
          Val x -> return (Val x)
          Var i | i `elem` is -> return (Var i)
                | otherwise   -> get >>= \ FLState { .. } -> case findBinding i heap of
                                                               Nothing -> return (Var i)
                                                               Just x  -> resolveFL' (i : is) x
          HaskellVal y -> return (HaskellVal y)

instantiate :: forall a. HasPrimitiveInfo a => ID -> FL a
instantiate i = case primitiveInfo @a of
  NoPrimitive -> msum (map update narrow)
    where update x = do
            x' <- share (return x) --TODO: share necessary because argument might be free calls that need to be shared
            FL $ do
             modify $ \ FLState { .. } -> FLState { heap = insertBinding i x' heap, .. }
             unFL x'
  Primitive   -> FL $ get >>= \ FLState { .. } -> unFL $ msum (map update (generate i constraintStore))
    where update x = do
            let c = eqConstraint (Var i) (Val x)
            let x' = return x --TODO: no share necessary because primitive types do not have arguments (that would be free otherwise)
            FL $ do
              modify $ \ FLState { .. } -> FLState { heap = insertBinding i x' heap
                                                   , constraintStore = insertConstraint c [i] constraintStore
                                                   , .. }
              unFL x'

{-
resolveFL :: FL a -> ND FLState (FLVal a)
resolveFL fl = unFL fl >>= \case
  Val x -> return (Val x)
  Var i -> get >>= \ FLState { .. } -> case findBinding i heap of
    Nothing -> return (Var i)
    Just x  -> return (Val x)

instantiate :: forall a. HasPrimitiveInfo a => ID -> ND FLState a
instantiate i = get >>= \ FLState { .. } ->
  case primitiveInfo @a of
    NoPrimitive -> msum (map update (narrow nextID))
      where update (x, o) = do
              put (FLState { nextID = nextID - o, heap = insertBinding i x heap, .. })
              return x
    Primitive   -> msum (map update (generate i constraintStore))
      where update x = do
              let c = eqConstraint (Var i) (Val x)
              put (FLState { heap =  insertBinding i x heap, constraintStore = insertConstraint c [i] constraintStore, .. })
              return x
-}

instance Monad FL where
  fl >>= f = FL $ resolveFL fl >>= unFL . \case
    Var i        -> instantiate i >>= f
    Val x        -> f x
    HaskellVal y -> f (to y)

instance Alternative FL where
  empty = FL empty
  FL a1 <|> FL a2 = FL (a1 <|> a2)

instance MonadPlus FL

instance MonadFail FL where
  fail s = FL (fail s)

instance MonadShare FL where
  share mx = memo (mx >>= shareArgs)

memo :: FL a -> FL (FL a)
memo fl = FL $ do
  i <- freshID
  unFL $ return $ FL $ do
    FLState { heap = heap1 } <- get --TODO: Perhaps use NamedFieldPuns?
    case findBinding i heap1 of
      Nothing -> unFL $ fl >>= \x -> FL $ do
        modify $ \ FLState { heap = heap2, .. } -> FLState { heap = insertBinding i x heap2, .. }
        return (Val x)
      Just x  -> return (Val x)

free :: HasPrimitiveInfo a => FL a
free = FL $ freshID >>= return . Var

free' :: HasPrimitiveInfo a => ID -> FL a
free' i = FL $ return $ Var i

--------------------------------------------------------------------------------

data Result (f :: Type -> Type) (a :: Type) where
  Result :: f a -> Result f a
  HaskellResult :: b -> Result f (Lifted (Result f) b)

class NormalForm a where
  normalFormWith :: Applicative m => (forall b. NormalForm b => FL (Lifted FL b) -> ND FLState (Result m (Lifted (Result m) b))) -> Lifted FL a -> ND FLState (Result m (Lifted (Result m) a))

-- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
-- Thus, we create the proof manually using unsafeCoerce
decomposeInjectivity :: Lifted m a ~ Lifted m b => a :~: b
decomposeInjectivity = unsafeCoerce Refl

groundNormalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> ND FLState (Result Identity (Lifted (Result Identity) a))
groundNormalFormFL fl = resolveFL fl >>= \case
  Val x -> normalFormWith groundNormalFormFL x
  Var i -> groundNormalFormFL (instantiate i)
  HaskellVal (y :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellResult y)

normalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> ND FLState (Result (Either ID) (Lifted (Result (Either ID)) a))
normalFormFL fl = resolveFL fl >>= \case
  Val x -> normalFormWith normalFormFL x
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
      NoPrimitive -> return (Result (Left i))
      Primitive   -> if isUnconstrained i constraintStore
                       then return (Result (Left i))
                       else normalFormFL (instantiate i)
  HaskellVal (y :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellResult y)

{-groundNormalFormFL :: NormalForm a => FL (Lifted FL a) -> ND FLState (Identity (Lifted Identity a))
groundNormalFormFL fl = resolveFL fl >>= \case
  Val x -> normalFormWith groundNormalFormFL x
  Var i -> instantiate i >>= normalFormWith groundNormalFormFL
  HaskellVal y ->

normalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> ND FLState (Either ID (Lifted (Either ID) a))
normalFormFL fl = resolveFL fl >>= \case
  Val x -> normalFormWith normalFormFL x
  {-
  x = JustFL (toFL (error "bla"))   ---> JustFL (Right (error "bla"))
  x = JustFL ()   ---> JustFL (error "bla"))
  Just
  -}
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
      NoPrimitive -> return (Left i)
      Primitive   -> if isUnconstrained i constraintStore
                       then return (Left i)
                       else instantiate i >>= normalFormWith normalFormFL-}

evalFLWith :: NormalForm a => (forall b. NormalForm b => FL (Lifted FL b) -> ND FLState (m (Lifted m b))) -> FL (Lifted FL a) -> [m (Lifted m a)]
evalFLWith nf fl = evalND (nf fl) initFLState

--TODO: mit dre run equality stimmt nicht ganz, da das nur für die grundnormalform gilt. für die normalform ist trotzdem noch evalFL x /= evalFL (x >>= return)

--------------------------------------------------------------------------------

--TODO: umbenennung bei input classes ist doof, weil die indizes verloren gehen könnten (id [var 1] [var 1] wird mit representanten zu var-1 oder so.)
--TODO: just use negative indices for fresh variables and keep the positve ones from input classes

class ShowFree a where
  showFree' :: a -> String
  showsFreePrec' :: Int -> a -> ShowS

  showFree' x = showsFreePrec' 0 x ""
  showsFreePrec' _ x s = showFree' x ++ s

--TODO: list syntax does not make much sense if there could(!) be free variables. we could only be sure if the list is finite and all tails are non-free. that cannot be tested.

showFree :: ShowFree a => a -> String
showFree x = showsFree x ""

showsFree :: ShowFree a => a -> ShowS
showsFree = showsFreePrec 0

showsFreePrec :: ShowFree a => Int -> a -> ShowS
showsFreePrec d x s = unsafePerformIO $ seq x (return (showsFreePrec' d x s)) `catch` (\ (FreeVariableException i) -> return $ showsVarPrec d i s)

showsVarPrec :: Int -> ID -> ShowS
showsVarPrec d i = showParen (d > 10) (showString ("var " ++ showsPrec 11 i ""))

--------------------------------------------------------------------------------

class To a where
  toWith :: (forall b. To b => b -> FL (Lifted FL b)) -> a -> Lifted FL a

to :: To a => a -> Lifted FL a
to = toWith toFL

toFL :: To a => a -> FL (Lifted FL a)
toFL x = FL (return (HaskellVal x))

class From a where
  fromWith :: (forall b. From b => m (Lifted m b) -> b) -> Lifted m a -> a

fromM :: forall m a. From a => (forall b. m b -> b) -> Result m (Lifted (Result m) a) -> a
fromM unM = \case
  HaskellResult (y :: b) -> case decomposeInjectivity @(Result m) @a @b of
    Refl -> y -- unsafeCoerce y
  Result x -> (fromWith (fromM unM) . unM) x

fromIdentity :: From a => Result Identity (Lifted (Result Identity) a) -> a
fromIdentity = fromM runIdentity

data FreeVariableException = FreeVariableException ID

instance Show FreeVariableException where
  show (FreeVariableException _) = "free variable occured"

instance Exception FreeVariableException

fromEither :: From a => Result (Either ID) (Lifted (Result (Either ID)) a) -> a
fromEither = fromM (either (throw . FreeVariableException) id)

--------------------------------------------------------------------------------

class Matchable a where
  match :: a -> Lifted FL a -> FL ()

matchFL :: forall a. (To a, Matchable a) => a -> FL (Lifted FL a) -> FL ()
matchFL x fl = FL $ resolveFL fl >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { heap = insertBinding i (toFL x) heap
                     , .. })
        return (Val ())
      Primitive   ->
        if isUnconstrained i constraintStore
          then do --TODO: fallunterscheidung tauschen. da nur variablen primitiven typs constrained sein können, kann man die unterscheidung von primitive und noprimitive eigentlich weglassen. @Kai: wie siehst du das? andererseits braucht man die primitiveinfo um den kontext zur verfügung zu haben....
            put (FLState { heap = insertBinding i (toFL x) heap
                         , .. })
            return (Val ())
          else
            let c = eqConstraint (Var i) (Val (to x))
                constraintStore' = insertConstraint c [i] constraintStore
            in if isConsistent constraintStore'
                 then do
                   put (FLState { heap = insertBinding i (toFL x) heap
                               , constraintStore = constraintStore'
                               , .. })
                   return (Val ())
                 else empty
  Val y  -> unFL $ match x y
  HaskellVal y -> unFL $ match x (to y)

-- linMatchFL :: forall a. (Convertible a, Matchable a) => a -> FL (Lifted a) -> FL ()
-- linMatchFL x (FL nd) = FL $ nd >>= \case
--   Var i -> lift get >>= \ (j, h, cst) -> do -- just do "update cst"
--     lift (put (j, insertBinding i (to x) h, cst))
--     return (Val ())
--   Val y -> unFL $ match x y

--------------------------------------------------------------------------------

class Unifiable a where
  lazyUnify :: Lifted FL a -> Lifted FL a -> FL ()

{-TODO:

type Output a = (Unifiable a, From a, NormalForm a)

type Input a = (To a, HasPrimitiveInfo (Lifted FL a))-}

--TODO: eigentlich nur narrowable notwendig --TODO: instantiateSameConstructor
narrowSameConstr :: (HasPrimitiveInfo (Lifted FL a), Unifiable a) => ID -> Lifted FL a -> FL ()
narrowSameConstr i x = instantiate i >>= flip lazyUnify x --TODO: discuss why this is inefficient

{-
narrowSame NilFL = NilFL
narrowSame (ConsFL _ _) = ConsFL free free
-}

lazyUnifyVar :: forall a. (Unifiable a, HasPrimitiveInfo (Lifted FL a)) => ID -> Lifted FL a -> FL ()
lazyUnifyVar i x = FL $ get >>= \ FLState { .. } ->
  case primitiveInfo @(Lifted FL a) of
    NoPrimitive -> do
      --TODO: just narrow a single constructor
      unFL $ narrowSameConstr i x
      {-
      x' <- share (return (narrowSame x) --TODO: share necessary because argument might be free calls that need to be shared
      FL $ do
        modify $ \ FLState { .. } -> FLState { heap = insertBinding i x' heap, .. }
        unFL x'

      update (narrowSame x)
      -}
    Primitive -> do
      let c = eqConstraint (Var i) (Val x)
      put (FLState { heap = insertBinding i (return @FL x) heap
                   , constraintStore = insertConstraint c [i] constraintStore, .. })
      return (Val ())

{-instance Unifiable a => Unifiable [a] where
  lazyUnifyVar j NilFL = FL $ get >>= \ FLState { .. } ->
    put (FLState { heap = insertBinding i fl1 heap
                , .. })
    return (Val ())
  lazyUnifyVar j (ConsFL x xs) = binde j an ConsFL (free h) (free i), 2 und mach lazyUnifyFL (free h) x und ....-}

-- output class lohnt sich für: $(inOutClassInv 'sort (Out [| [LT, var 1, GT] |] [| var 1 : var 2 |]))
-- $(inOutClassInv 'sort (Out [| [LT, var 1, GT] |] [| var 2 | ]))

-- $(inOutClassInv 'f (Out [| Just (var 1) |]) [| var 2 |])
-- f (Just x) = not x
-- f Nothing = False

--TODO: flip, rename fl1 to flx etc.
--TODO: check lazyUnifyFL (x, failed) (y,y)
lazyUnifyFL :: forall a. Unifiable a => FL (Lifted FL a) -> FL (Lifted FL a) -> FL ()
lazyUnifyFL fl1 fl2 = FL $ resolveFL fl2 >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { heap = insertBinding i fl1 heap
                     , .. })
        return (Val ())
      Primitive   ->
        if isUnconstrained i constraintStore
          then do
            put (FLState { heap = insertBinding i fl1 heap
                         , .. })
            return (Val ())
          else --TODO: i ist constrained, also müssen wir uns den anderen wert anschauen, um zu checken, ob er einem bereits bestehenden constraint widerspricht
            resolveFL fl1 >>= \case
              Var j ->
                let c = eqConstraint @(Lifted FL a) (Var i) (Var j)
                    constraintStore' = insertConstraint c [i, j] constraintStore
                in if isConsistent constraintStore'
                     then do
                       put (FLState { heap = insertBinding i (FL (return (Var @(Lifted FL a) j))) heap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
              Val x ->
                let c = eqConstraint (Var i) (Val x)
                    constraintStore' = insertConstraint c [i] constraintStore
                in if isConsistent constraintStore'
                     then do
                       put (FLState { heap = insertBinding i (return @FL x) heap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
              HaskellVal y ->
                let x = to y in
                let c = eqConstraint (Var i) (Val x)
                    constraintStore' = insertConstraint c [i] constraintStore
                in if isConsistent constraintStore'
                     then do
                       put (FLState { heap = insertBinding i (return @FL x) heap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
  Val y  -> resolveFL fl1 >>= \case
    Var j -> unFL $ lazyUnifyVar j y
    Val x -> unFL $ lazyUnify x y
    HaskellVal x -> unFL $ lazyUnify (to x) y
  HaskellVal y -> resolveFL fl1 >>= \case
    Var j -> unFL $ lazyUnifyVar j (to y)
    Val x -> unFL $ lazyUnify x (to y)
    HaskellVal x -> unFL $ lazyUnify @a (to x) (to y) --TODO


-- "unify (error "bla") (var 1)" zeigt, dass es notwendig ist, dass man wissen muss ob 1 unconstrained ist.
-- var 1 == var 2
-- var 1 == var _

-- $(inOutClassInv 'id (Out [| var 1 |]) [| 3 |])
-- $(inOutClassInv 'id (Out [| 3 |]) [| var 1 |])

-- unifyFL (error "bla") (var 1)

-- f x = (x, if x == 42 then False else True)
-- unifyFL (43, False) $ fFL (var 1)
-- unifyFL (43, False) $ (var 1, )

-- g x y = (if x == y then False else True, x)

-- (1, error "bla") (var 1, var 1)
-- (1, var 1) (var 1, var 1)
--------------------------------------------------------------------------------

--TODO: no longer needed, just for sanity checking if all necessary instances are defined for built-in types
class (From a, To a, Matchable a, Unifiable a, NormalForm a, Shareable FL (Lifted FL a), HasPrimitiveInfo (Lifted FL a), ShowFree a) => Invertible a

--------------------------------------------------------------------------------

--TODO: move?! But where to?
infixr 0 :-->
type (:-->) = (-->) FL --TODO: move to util. gehört aber eigentlich auch nicht hier hin.

newtype (-->) (m :: Type -> Type) (a :: Type) (b :: Type) = Func (m a -> m b)

infixr 0 -->

type instance Lifted m (->) = (-->) m
type instance Lifted m ((->) a) = (-->) m (Lifted m a)
type instance Lifted m ((->) a b) = (-->) m (Lifted m a) (Lifted m b)

instance (From a, NormalForm a, To b) => To (a -> b) where
  toWith _ f = Func $ \x -> FL $ groundNormalFormFL x >>= (unFL . toFL' . f . fromIdentity)

instance MonadShare m => Shareable m ((-->) m a b) where
  shareArgs (Func !f) = return (Func f)

appFL :: Monad m => m ((-->) m a b) -> m a -> m b
mf `appFL` x = mf >>= \ (Func f) -> f x

-- This function incorporates the improvement from the paper for
-- partial values in the context of partial inversion with higher-order functions.
toFL' :: To a => a -> FL (Lifted FL a)
toFL' x | isBottom x = empty
        | otherwise  = return (toWith toFL' x)

type Input a = (To a, Unifiable a)
type Output a = (From a, HasPrimitiveInfo (Lifted FL a), NormalForm a)
