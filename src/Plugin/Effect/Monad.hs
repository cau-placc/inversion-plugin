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
{-# LANGUAGE QuantifiedConstraints     #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilyDependencies    #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}

{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Plugin.Effect.Monad where

import Control.Applicative             (Alternative(..))
import Control.Exception
import Control.Monad.Identity
import Control.Monad.State

import           Data.Kind                 (Type)
import qualified Data.Kind
import           Data.Map                  (Map)
import qualified Data.Map           as Map
import           Data.Set                  (Set)
import qualified Data.Set           as Set
import           Data.Typeable             (type (:~:)(..))

#ifdef USE_WHAT4
import Plugin.Effect.SolverLibrary.What4 ()
#elif defined(USE_SBV)
import Plugin.Effect.SolverLibrary.SBV   ()
#else
#error No solver library specified
#endif
import Plugin.Effect.Tree
import Plugin.Lifted

import System.IO.Unsafe (unsafePerformIO)

import Test.ChasingBottoms.IsBottom (isBottom)

import Unsafe.Coerce (unsafeCoerce)

--------------------------------------------------------------------------------

class Monad m => MonadShare m where
  share :: m a -> m (m a)

--------------------------------------------------------------------------------

type ID = Int --TODO: Enum voraussetzen, damit man mit pred den vrogänger berechnen kann. Id muss als schlüssel für den Heap verwendet werden können (d.h. im normalfall mindestens eq), integer ist ein guter wert, in der praxis

--TODO: Rename heap to Dict, store, map
type Heap a = Map ID a --TODO: intmap oder gar intmap von maja r.
-- [(ID, a)]


{-class
  type ID
  type
  emptyMap -}

-- type Heap a

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

type ND s = StateT s Search

evalND :: NDState s => ND s a -> [a]
evalND nd = search (searchTree (evalStateT nd initNDState))
  where
#ifdef USE_DFS
    search = dfs
#elif defined(USE_IDDFS)
    search = iddfs
#elif defined(USE_BFS)
    search = bfs
#elif defined(USE_PS)
    search = bfs
#else
#error No search strategy specified
#endif

class NDState s where
  initNDState :: s
  memoID      :: s -> ID
  setMemoID   :: ID -> s -> s
  memoMap     :: s -> Map ID Untyped
  setMemoMap  :: Map ID Untyped -> s -> s

freshMemoID :: NDState s => ND s ID
freshMemoID = do
  i <- gets memoID
  modify (setMemoID (succ i))
  return i

-- Note: This requires the TypeSynonymInstances language extension.
instance NDState s => MonadShare (ND s) where
  share mx = do
    i <- freshMemoID
    return $ do
      m <- gets memoMap
      case findBinding i m of
        Nothing -> mx >>= \x -> do
          modify (\s -> setMemoMap (insertBinding i x (memoMap s)) s)
          return x
        Just x  -> return x

--TODO: memo auslagern

{-
type ND1 s = StateT s SearchTree

evalND1 :: NDState s => ND1 s a -> s -> Tree a
evalND1 = evalStateT

type ND2 s = StateT s (Codensity SearchTree)

evalND2 :: NDState s => ND3 s a -> s -> SearchTree a
evalND2 nd s = runCodensity (evalStateT nd s) return
-}

--------------------------------------------------------------------------------

class Narrowable a where
  narrow :: [FL a]
  --TODO: narrowSameConstr :: a -> a

--TODO: narrow same constructor als remark?

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

data PrimitiveInfo a = Narrowable a => NoPrimitive
                     | Constrainable a => Primitive

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a

--------------------------------------------------------------------------------

{-
data FLVal a = HasPrimitiveInfo a => Var ID | Val a
-}

data FLVal (a :: Type) where
  Var        :: HasPrimitiveInfo a => ID -> FLVal a
  Val        :: a -> FLVal a
  HaskellVal :: To b => b -> FLVal (Lifted FL b)
  --TODO: reihenfolge der konstruktoren umändern...

  --TODO: stark ähnlich zu uneval von den set functions. nur war da die idee, dass der wert nicht umgewandelt werden muss, sondern der effekt da einfach unausgewertet drin stecken kann. bei der normalform berechnung müsste man einen weg haben, diesen wert nicht weiter anzuschauen

--------------------------------------------------------------------------------

-- data FLState2 = FLState2 {
--     nextID2          :: ID,
--     heap2            :: Heap Untyped,
--     nextVarID        :: ID,
--     varHeap          :: Heap Untyped,
--     constraintStore2 :: ConstraintStore
--   }

--TODO: Rename heap to store

{-
varHeap:
match-Setting:
ID -> a (mit a FL-gelifted HNF)
unify-Setting:
ID -> FL a (also ganze monadische berechnungen, die lazy gebindet werden können)

memoHeap:
ID -> FLVal a

lookupHeap :: ID -> Heap -> a
lookupHeap :: ID -> Heap -> Maybe (FLVal a)
insertHeap :: ID -> FLVal a -> Heap -> Heap
-}

--nextID :: ID -> ID
--nextID = pred

data FLState = FLState {
    {-memoID          :: ID,
    memoMap         :: Heap Untyped
    varID           :: ID
    varMap          :: Heap Untyped,-}
    _memoID :: ID,
    _memoMap :: Heap Untyped,
    varID :: ID,
    varHeap :: Heap Untyped,
    constraintStore :: ConstraintStore
  }

instance NDState FLState where
  memoID = _memoID
  memoMap = _memoMap
  setMemoID i s = s { _memoID = i }
  setMemoMap m s = s { _memoMap = m }
  initNDState = FLState {
      _memoID = 0,
      _memoMap = emptyHeap,
      varID = -1,
      varHeap = emptyHeap,
      constraintStore = initConstraintStore
    }

freshVarID :: ND FLState ID
freshVarID = do
    i <- gets varID
    modify (\s -> s { varID = pred i })
    --trace (show i) $ return i
    return i

--------------------------------------------------------------------------------

newtype FL a = FL { unFL :: ND FLState (FLVal a) }

evalFL :: FL a -> [FLVal a]
evalFL fl = evalND (unFL fl)

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
                | otherwise   -> get >>= \ FLState { .. } -> case findBinding i varHeap of
                                                               Nothing -> return (Var i)
                                                               Just x  -> resolveFL' (i : is) x
          HaskellVal y -> return (HaskellVal y)

instantiate :: forall a. HasPrimitiveInfo a => ID -> ND FLState a
instantiate i = case primitiveInfo @a of
  NoPrimitive -> msum (map update narrow)
    where update (FL ndx) = do
            Val x <- ndx
            modify $ \ FLState { .. } -> FLState { varHeap = insertBinding i (return @FL x) varHeap, .. } --TODO: in der ersten version sind auf dem heap noch keine fl a berechnungen, sondern nur lifted as
            return x
  Primitive   -> get >>= \ FLState { .. } -> msum (map update (generate i constraintStore))
    where update x = do
            let c = eqConstraint (Var i) (Val x)
            modify $ \ FLState { .. } -> FLState { varHeap = insertBinding i (return @FL x) varHeap
                                                 , constraintStore = insertConstraint c [i] constraintStore
                                                 , .. }
            return x

-- instantiate :: forall a. HasPrimitiveInfo a => ID -> FL a
-- instantiate i = case primitiveInfo @a of
--   NoPrimitive -> msum (map update narrow)
--     where update x = do
--             x' <- share (return x) --TODO: share necessary because argument might be free calls that need to be shared
--             FL $ do
--               modify $ \ FLState { .. } -> FLState { varHeap = insertBinding i x' varHeap, .. } --TODO: in der ersten version sind auf dem heap noch keine fl a berechnungen, sondern nur lifted as
--               unFL x' --TODO remove
--   Primitive   -> FL $ get >>= \ FLState { .. } -> unFL $ msum (map update (generate i constraintStore))
--     where update x = do
--             let c = eqConstraint (Var i) (Val x)
--             let x' = return x --TODO: no share necessary because primitive types do not have arguments (that would be free otherwise)
--             FL $ do
--               modify $ \ FLState { .. } -> FLState { varHeap = insertBinding i x' varHeap
--                                                    , constraintStore = insertConstraint c [i] constraintStore
--                                                    , .. }
--               unFL x'

-- instantiate :: forall a. HasPrimitiveInfo a => ID -> ND FLState (FLVal a)
-- instantiate i = case primitiveInfo @a of
--   NoPrimitive -> msum (map update narrow)
--     where update x = do
--             x' <- share (return (Val x)) --TODO: share necessary because argument might be free calls that need to be shared
--             modify $ \ FLState { .. } -> FLState { varHeap = insertBinding i x' varHeap, .. }
--             x'
--   Primitive   -> get >>= \ FLState { .. } -> msum (map update (generate i constraintStore))
--     where update x = do
--             let c = eqConstraint (Var i) (Val x)
--             let x' = return x --TODO: no share necessary because primitive types do not have arguments (that would be free otherwise)
--             modify $ \ FLState { .. } -> FLState { varHeap = insertBinding i x' varHeap
--                                                    , constraintStore = insertConstraint c [i] constraintStore
--                                                    , .. }
--             x'

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
  fl >>= f = FL $ resolveFL fl >>= \case
    Var i        -> instantiate i >>= unFL . f
    Val x        -> unFL (f x)
    HaskellVal y -> unFL (f (to y))

instance Alternative FL where
  empty = FL empty
  FL a1 <|> FL a2 = FL (a1 <|> a2)

instance MonadPlus FL

instance MonadFail FL where
  fail s = FL (fail s)

instance MonadFix FL where
  mfix f = FL $ mfix (unFL . f . unVal)
    where
      unVal (Val x) = x
      unVal _ = error "Not a Val in mfix"

instance MonadShare FL where
  share fl = FL (fmap (Val . FL) (share (unFL fl)))

free :: HasPrimitiveInfo a => FL a
free = FL (Var <$> freshVarID)

--------------------------------------------------------------------------------


-- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
-- Thus, we create the proof manually using unsafeCoerce
decomposeInjectivity :: Lifted m a ~ Lifted m b => a :~: b
decomposeInjectivity = unsafeCoerce Refl

class NormalForm a where
  normalFormWith :: (forall b. NormalForm b => FL (Lifted FL b) -> FL (Lifted FL b)) -> Lifted FL a -> FL (Lifted FL a)
  --TODO: normalForm and groundNormalForm...

--TODO: rename haskellval y to haskellval x overall
groundNormalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> FL (Lifted FL a)
groundNormalFormFL fl = FL $ resolveFL fl >>= \case
  Var i -> instantiate i >>= unFL . normalFormWith groundNormalFormFL
  Val x -> unFL $ normalFormWith groundNormalFormFL x
  HaskellVal (x :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellVal x)
--TODO: Alternatively:
--groundNormalFormFL fl = fl >>= normalFormWith groundNormalFormFL

normalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> FL (Lifted FL a)
normalFormFL fl = FL $ resolveFL fl >>= \case
  Var i -> case primitiveInfo @(Lifted FL a) of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
    NoPrimitive -> return (Var i)
    Primitive   -> get >>= \ FLState { .. } ->
      if isUnconstrained i constraintStore
        then return (Var i)
        else instantiate i >>= unFL . normalFormWith normalFormFL
  Val x -> unFL $ normalFormWith normalFormFL x
  HaskellVal (x :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellVal x)

{-groundNormalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> ND FLState (Result Identity (Lifted (Result Identity) a))
groundNormalFormFL fl = resolveFL fl >>= \case
  Val x -> normalFormWith groundNormalFormFL x
  Var i -> groundNormalFormFL (instantiate i)
  HaskellVal (y :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellResult y)-}

{-normalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> ND FLState (Result (Either ID) (Lifted (Result (Either ID)) a))
normalFormFL fl = resolveFL fl >>= \case
  Val x -> normalFormWith normalFormFL x
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
      NoPrimitive -> return (Result (Left i))
      Primitive   -> if isUnconstrained i constraintStore
                       then return (Result (Left i))
                       else normalFormFL (instantiate i)
  HaskellVal (y :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellResult y)-}
{-
FL $ nd >>= \case
  Val x -> unFL $ nf normalFormFL x
  Var i -> get >>= \FLState { .. } -> case findBinding i heap of
    Nothing -> return (Var i)
    Just x  -> unFL $ nf normalFormFL x
    -}

-- TODO: we could just use >>= here, but this would be more strict on haskellvals than needed.
-- groundNormalFormFL :: NormalForm a => FL a -> FL a
-- groundNormalFormFL fl = FL $ resolveFL fl >>= \case
--   Val x        -> unFL $ normalFormWith groundNormalFormFL x
--   Var i        -> unFL $ groundNormalFormFL (instantiate i)
--   HaskellVal y -> return (HaskellVal y)

-- normalFormFL :: forall a. NormalForm a => FL a -> FL a
-- normalFormFL fl = FL $ resolveFL fl >>= \case
--   Val x -> unFL $ normalFormWith normalFormFL x
--   Var i -> get >>= \ FLState { .. } ->
--     case primitiveInfo @a of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
--       NoPrimitive -> return (Var i)
--       Primitive   -> if isUnconstrained i constraintStore
--                        then return (Var i)
--                        else unFL $ normalFormFL (instantiate i)
--   HaskellVal y -> return (HaskellVal y)

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

--evalFLWith :: NormalForm a => (forall b. NormalForm b => FL (Lifted FL b) -> ND FLState (m (Lifted m b))) -> FL (Lifted FL a) -> [m (Lifted m a)]
--evalFLWith nf fl = evalND (nf fl) initFLState
--map fromFLVal $ evalFL (groundNormalFormFL ...)

{-
groundNormalFormFL :: FL (a :--> a)
groundNormalFormFL = return $ Func $ gnfFL :: FL a -> FL a

($###) :: FL ((a :--> b) :--> a :--> b)
($###) = return $ Func $ \f -> return $ Func $ \x -> groundNormalForm x >>= \x' -> f `appFL` return x'

(=:<=#) :: FL (a :--> a :--> BoolFL FL)
(=:<=#) = return $ Func $ \x -> return $ Func $ \y -> flip unifyFL x y >> return TrueFL

gnf :: Lifted FL a -> FL a

gnf :: FL (Lifted FL a) -> ND _ a


gnf :: Lifted FL a -> FL (Lifted (Either ID) a)
gnf NilFL = return NilFL
gnf (ConsFL x xs) = unFL (gnfFL x) ...

gnfFL :: FL (Lifted FL a) -> FL (Lifted (Result (Either ID)) a)
gnfFL fl = unFL fl >>= \case
  HaskellVal y -> --TODO: geht nicht ohne result
-}

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
  --TODO: remark: id2Test = $(inv 'id2 True) ("hello" ++ loop); als grund dafür, dass es kein showFreeList gibt, da man dann gucken müsste, ob die liste endlich ist und alle tails non-free sind. dann würde obige ausgabe sich anders verhalten als mit show.

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
  --TODO: to and to'

to :: To a => a -> Lifted FL a
to = toWith toFL

toFL :: To a => a -> FL (Lifted FL a)
toFL x = FL (return (HaskellVal x))
--TODO: Alternatively: toFL x = return (to x)

class From a where
  from :: Lifted FL a -> a

data FreeVariableException = FreeVariableException ID

instance Show FreeVariableException where
  show (FreeVariableException _) = "free variable occured"

instance Exception FreeVariableException

fromFLVal :: forall a. From a => FLVal (Lifted FL a) -> a
fromFLVal = \case
   Val x -> from x
   Var i -> throw (FreeVariableException i)
   HaskellVal (y :: b) -> case decomposeInjectivity @FL @a @b of
     Refl -> y

fromFL :: From a => FL (Lifted FL a) -> a
fromFL fl = fromFLVal (head (evalFL fl))

{-class From a where
  fromWith :: (forall b. From b => m (Lifted m b) -> b) -> Lifted m a -> a

fromM :: forall m a. From a => (forall b. m b -> b) -> Result m (Lifted (Result m) a) -> a
fromM unM = \case
  HaskellResult (y :: b) -> case decomposeInjectivity @(Result m) @a @b of
    Refl -> y -- unsafeCoerce y
  Result x -> (fromWith (fromM unM) . unM) x

fromIdentity :: From a => Result Identity (Lifted (Result Identity) a) -> a
fromIdentity = fromM runIdentity

fromEither :: From a => Result (Either ID) (Lifted (Result (Either ID)) a) -> a
fromEither = fromM (either (throw . FreeVariableException) id)-}


-- class From a where
--   fromWith :: (forall b. From b => FL (Lifted FL b) -> b) -> Lifted FL a -> a
-- --fromFL2 :: FL (Lifted FL a) -> FL a
-- --from2 :: Lifted FL a -> FL a

-- fromFLVal :: forall a. From a => FLVal (Lifted FL a) -> a
-- fromFLVal = \case
--   Val x -> fromWith fromFL x
--   Var i -> throw (FreeVariableException i)
--   HaskellVal (y :: b) -> case decomposeInjectivity @FL @a @b of
--     Refl -> y
{-
narrowSameConstr NilFL = NilFL
narrowSameConstr (ConsFL _ _) = ConsFL free free
-}

--------------------------------------------------------------------------------

{-data FLVal1 a = Val1 { unVal1 :: a } | Var1 ID

data FLVal2 a where
  Val2 :: a -> FLVal2 a
  Var2 :: ID -> FLVal2 a
  HaskellVal2 :: To a => a -> FLVal2 (Lifted FL a)

unVal2 :: FLVal2 a -> a
unVal2 (Val2 x) = x
unVal2 (HaskellVal2 x) = to x

fromFLVal1 :: From a => FLVal1 (Lifted FL a) -> a
fromFLVal1 = \case
  Var1 i        -> throw (FreeVariableException i)
  x            -> from (unVal1 x)

fromFLVal2 :: From a => FLVal2 (Lifted FL a) -> a
fromFLVal2 = \case
  Var2 i        -> throw (FreeVariableException i)
  x            -> from (unVal2 x)
-}

--------------------------------------------------------------------------------

class Unifiable a where
  unify :: Lifted FL a -> Lifted FL a -> FL ()
  lazyUnify :: Lifted FL a -> Lifted FL a -> FL ()

{-TODO:

type Output a = (Unifiable a, From a, NormalForm a)

type Input a = (To a, HasPrimitiveInfo (Lifted FL a))-}

--TODO: eigentlich nur narrowable notwendig --TODO: instantiateSameConstructor
instantiateSameConstructor :: (HasPrimitiveInfo (Lifted FL a), Unifiable a) => Lifted FL a -> ID -> FL ()
instantiateSameConstructor x i = FL $ instantiate i >>= unFL . lazyUnify x --TODO: discuss why this is inefficient

{-
narrowSame NilFL = NilFL
narrowSame (ConsFL _ _) = ConsFL free free
-}

unifyFL :: forall a. Unifiable a => FL (Lifted FL a) -> FL (Lifted FL a) -> FL ()
unifyFL fl1 fl2 = FL $ do
  nd1 <- resolveFL fl1
  nd2 <- resolveFL fl2
  FLState { .. } <- get
  case (nd1, nd2) of
    (Var i, Var j)
      | i == j -> return (Val ())
      | otherwise -> case primitiveInfo @(Lifted FL a) of
        NoPrimitive -> do
          put (FLState { varHeap = insertBinding i (FL (return nd2)) varHeap
                       , .. })
          return (Val ())
        Primitive -> let c = eqConstraint @(Lifted FL a) (Var i) (Var j)
                         constraintStore' = insertConstraint c [i, j] constraintStore
                     in if isUnconstrained i constraintStore || isUnconstrained j constraintStore || isConsistent constraintStore'
                          then do
                            put (FLState { varHeap = insertBinding i (FL (return nd2)) varHeap
                                         , constraintStore = constraintStore'
                                         , .. })
                            return (Val ())
                          else empty
    (Var i, Val y) -> unFL $ unifyVar y i
    (Val x, Var j) -> unFL $ unifyVar x j
    (Val x, Val y) -> unFL $ unify x y
    (Var i, HaskellVal y) -> unFL $ unifyVar (to y) i
    (Val x, HaskellVal y) -> unFL $ unify x (to y)
    (HaskellVal x, Var j) -> unFL $ unifyVar (to x) j
    (HaskellVal x, Val y) -> unFL $ unify (to x) y
    (HaskellVal x, HaskellVal y) -> unFL $ unify (to x) (to y)

--TODO: unifyVar und lazyUnifyVar funktionieren quasi gleich. da eines immer eine variable ist und das andere immer ein konstruktor (oder eine variable), passiert da eigentlich nichts unterscheidliches, oder?
unifyVar :: forall a. (Unifiable a, HasPrimitiveInfo (Lifted FL a)) => Lifted FL a -> ID -> FL ()
unifyVar x i = FL $ get >>= \ FLState { .. } ->
  case primitiveInfo @(Lifted FL a) of
    NoPrimitive -> instantiate i >>= unFL . unify x --TODO: instantiateSameConstructor i x anstelle von instantiate i
    Primitive -> let c = eqConstraint (Var i) (Val x)
                     constraintStore' = insertConstraint c [i] constraintStore
                 in if isUnconstrained i constraintStore || isConsistent constraintStore'
                      then do
                        put (FLState { varHeap = insertBinding i (return @FL x) varHeap
                                     , constraintStore = constraintStore'
                                     , .. })
                        return (Val ())
                      else empty --TODO: auslagern

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
lazyUnifyFL fl1 fl2 = FL $ resolveFL fl1 >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { varHeap = insertBinding i fl2 varHeap
                     , .. })
        return (Val ())
      Primitive   ->
        if isUnconstrained i constraintStore
          then do
            put (FLState { varHeap = insertBinding i fl2 varHeap
                         , .. })
            return (Val ())
          else --i ist constrained, also müssen wir uns den anderen wert anschauen, um zu checken, ob er einem bereits bestehenden constraint widerspricht
            resolveFL fl2 >>= \case
              Var j -> --TODO: kai: add check if i == j. und außerdem kann es sein, dass j unconstrained ist. dann kann j nichts ändern
                let c = eqConstraint @(Lifted FL a) (Var i) (Var j)
                    constraintStore' = insertConstraint c [i, j] constraintStore
                in if isUnconstrained j constraintStore || isConsistent constraintStore'
                     then do
                       put (FLState { varHeap = insertBinding i (FL (return (Var @(Lifted FL a) j))) varHeap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
              Val x ->
                let c = eqConstraint (Var i) (Val x)
                    constraintStore' = insertConstraint c [i] constraintStore
                in if isConsistent constraintStore'
                     then do
                       put (FLState { varHeap = insertBinding i (return @FL x) varHeap
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
                       put (FLState { varHeap = insertBinding i (return @FL x) varHeap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
  Val x  -> resolveFL fl2 >>= \case
    Var j        -> unFL $ lazyUnifyVar x j
    Val y        -> unFL $ lazyUnify x y
    HaskellVal y -> unFL $ lazyUnify x (to y)
  HaskellVal x -> resolveFL fl2 >>= \case
    Var j        -> unFL $ lazyUnifyVar (to x) j
    Val y        -> unFL $ lazyUnify (to x) y
    HaskellVal y -> unFL $ lazyUnify @a (to x) (to y)

--TODO: unifyVarWith?
lazyUnifyVar :: forall a. (Unifiable a, HasPrimitiveInfo (Lifted FL a)) => Lifted FL a -> ID -> FL ()
lazyUnifyVar x i = FL $ get >>= \ FLState { .. } ->
  case primitiveInfo @(Lifted FL a) of
    NoPrimitive -> instantiate i >>= unFL . lazyUnify x --TODO: instantiateSameConstructor i x anstelle von instantiate i
    Primitive -> let c = eqConstraint (Var i) (Val x)
                     constraintStore' = insertConstraint c [i] constraintStore
                 in if isUnconstrained i constraintStore || isConsistent constraintStore'
                      then do
                        put (FLState { varHeap = insertBinding i (return @FL x) varHeap
                                     , constraintStore = constraintStore'
                                      , .. })
                        return (Val ())
                      else empty --TODO: auslagern

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
class (From a, To a, Unifiable a, NormalForm a, HasPrimitiveInfo (Lifted FL a), ShowFree a) => Invertible a

--------------------------------------------------------------------------------

--TODO: move?! But where to?
infixr 0 :-->
type (:-->) = (-->) FL --TODO: move to util. gehört aber eigentlich auch nicht hier hin.

newtype (-->) (m :: Type -> Type) (a :: Type) (b :: Type) = Func (m a -> m b)

--remark: newtype um instanzen angeben zu können und typklassen (partielle applikation ,e.g. functor, unterstützen)

infixr 0 -->

type instance Lifted m (->) = (-->) m
type instance Lifted m ((->) a) = (-->) m (Lifted m a)
type instance Lifted m ((->) a b) = (-->) m (Lifted m a) (Lifted m b)

instance (From a, NormalForm a, To b) => To (a -> b) where
  toWith _ f = Func $ \x -> toFL' (f (fromFL (groundNormalFormFL x)))
  --toWith _ f = Func $ \x -> FL $ groundNormalFormFL x >>= (unFL . toFL' . f . fromIdentity)
--instance (From a, NormalForm (Lifted FL a), To b) => To (a -> b) where
  --toWith _ f = Func $ \x -> toFL' (f (fromFL (groundNormalFormFL x)))

appFL :: Monad m => m ((-->) m a b) -> m a -> m b
mf `appFL` mx = mf >>= \ (Func f) -> f mx

appShareFL :: MonadShare m => m ((-->) m a b) -> m a -> m b
appShareFL mf mx = share mx >>= appFL mf

-- This function incorporates the improvement from the paper for
-- partial values in the context of partial inversion with higher-order functions.
toFL' :: To a => a -> FL (Lifted FL a)
toFL' x | isBottom x = empty
        | otherwise  = return (toWith toFL' x)

type Input a = (To a, Unifiable a)
type Output a = (From a, HasPrimitiveInfo (Lifted FL a), NormalForm a) --TODO: Get rid of the tpye family maybe?
