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

 -- Note: Adding MonadShare m here as a constraint leads to a bug in the plugin when a quantified constraint occurs.
class Shareable m a where
  shareArgs :: a -> m a

type ID = Int --TODO: Enum voraussetzen, damit man mit pred den vrogänger berechnen kann. Id muss als schlüssel für den Heap verwendet werden können (d.h. im normalfall mindestens eq), integer ist ein guter wert, in der praxis

class ShareState s where
  memoID :: s -> ID
  setMemoID :: ID -> s -> s
  memoMap :: s -> Map ID Untyped
  setMemoMap :: Map ID Untyped -> s -> s

freshMemoID :: (ShareState s, MonadState s m) => m ID
freshMemoID = do
  i <- gets memoID
  modify (setMemoID (pred i))
  return i

-- Note: This requires the TypeSynonymInstances language extension.
instance {-# OVERLAPPABLE #-} (ShareState s, Monad m, MonadState s m) => MonadShare m where --TODO: remove Monad ma nd overlappable for the diss
  share mx = do
    i <- freshMemoID
    return $ do
      m <- gets memoMap
      case findBinding i m of
        Nothing -> mx >>= shareArgs >>= \x -> do
          modify (\s -> setMemoMap (insertBinding i x (memoMap s)) s)
          return x
        Just x  -> return x

--------------------------------------------------------------------------------



--------------------------------------------------------------------------------

type ND s = StateT s Search

evalND :: ND s a -> s -> [a]
evalND nd s = search (searchTree (evalStateT nd s))
  where
#ifdef DEPTH_FIRST
    search = dfs
#elif defined(PARALLEL)
    search = ps
#else
    search = bfs
#endif

{-
type ND1 s = StateT s SearchTree

evalND1 :: NDState s => ND1 s a -> s -> Tree a
evalND1 = evalStateT

type ND2 s = StateT s (Codensity SearchTree)

evalND2 :: NDState s => ND3 s a -> s -> SearchTree a
evalND2 nd s = runCodensity (evalStateT nd s) return
-}

--------------------------------------------------------------------------------

--TODO: Rename heap to Dict, store, map
type Heap a = Map ID a --TODO: intmap oder gar intmap von maja r.


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

{-
data FLVal a = HasPrimitiveInfo a => Var ID | Val a
-}

data FLVal (a :: Type) where
  Var        :: HasPrimitiveInfo a => ID -> FLVal a
  Val        :: a -> FLVal a
  HaskellVal :: To b => b -> FLVal (Lifted FL b)

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
    nextID :: ID,
    heap :: Heap Untyped,
    constraintStore :: ConstraintStore
  }
--TODO: getrennter heap?

instance ShareState FLState where
  memoID = nextID
  memoMap = heap
  setMemoID i s = s { nextID = i }
  setMemoMap m s = s { heap = m }

initFLState :: FLState
initFLState = FLState {
    {-memoID          = -1,
    memoMap         = emptyHeap,
    varID           = -1,
    varMap          = emptyHeap-}
    nextID = -1,
    heap = emptyHeap,
    constraintStore = initConstraintStore
  }

freshID :: ND FLState ID
freshID = freshMemoID

--------------------------------------------------------------------------------

--TODO: begründung: wenn ich shareable fl habe, kann ich daraus das shareable auf nd ebene konstruieren. das brauche ich, weil für die komponenten, der werte, die ich auf nd ebene share und die in fl sind (wofür ich shareabgle habe), in der nd monade sharen möchte (weil ich die share von der nd-instanz verwende).
instance Shareable FL a => Shareable (ND FLState) (FLVal a) where
  shareArgs (Var i)        = return (Var i)
  shareArgs (Val x)        = unFL (shareArgs x)
  shareArgs (HaskellVal y) = return (HaskellVal y)

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

instance MonadFix FL where
  mfix f = FL $ mfix (unFL . f . unVal)
    where
      unVal (Val x) = x
      unVal _ = error "Not a Val in mfix"

instance MonadShare FL where
  share fl = FL (fmap (Val . FL) (share (unFL fl)))

free :: HasPrimitiveInfo a => FL a
free = FL $ freshID >>= return . Var

--------------------------------------------------------------------------------

data Result (f :: Type -> Type) (a :: Type) where
  Result :: f a -> Result f a
  HaskellResult :: b -> Result f (Lifted (Result f) b)
-- {-data Result (f :: Type -> Type) (a :: Type) where
--   Result :: f a -> Result f a
--   HaskellResult :: b -> Result f (Lifted (Result f) b)-}

class NormalForm1 a where
  normalFormWith1 :: Applicative m => (forall b. NormalForm b => FL (Lifted FL b) -> ND FLState (Result m (Lifted (Result m) b))) -> Lifted FL a -> ND FLState (Result m (Lifted (Result m) a))
-- class NormalForm a where
--   normalFormWith :: (forall b. NormalForm b => FL b -> FL b) -> a -> FL a

-- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
-- Thus, we create the proof manually using unsafeCoerce
decomposeInjectivity :: Lifted m a ~ Lifted m b => a :~: b
decomposeInjectivity = unsafeCoerce Refl

--groundNormalFormFL :: FL a -> FL a

-- groundNormalFormFL :: FL a -> ND FLState (Identity (TODO Identity a))
--TODO m (BoolM FL) = BoolM m
--TODO m (ListM FL) = ListM m
--TODO m (ListM FL a) = ListM m (TODO m a)
-- groundNormalFormFL :: FL (Lifted FL a) -> ND FLState (Identity (Lifted Identity a))

--evalFL' :: FL a -> ND FLState a
--evalND :: ND s a -> s -> [a]

--evalFL :: FL a -> [a]
--evalFL ... = evalND

-- evalFL :: FL (Lifted FL a) -> [Lifted FL a]

-- from :: Lifted FL a -> a
--

class NormalForm2 a where
  normalForm2 :: Lifted FL a -> ND FLState (FLVal (Lifted FL a))
class NormalForm a where
  normalFormWith :: (forall b. NormalForm b => FL (Lifted FL b) -> FL (Lifted FL b)) -> Lifted FL a -> FL (Lifted FL a)

--TODO: rename haskellval y to haskellval x overall
groundNormalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> FL (Lifted FL a)
groundNormalFormFL fl = FL $ resolveFL fl >>= \case
  Var i -> unFL $ groundNormalFormFL (instantiate i)
  Val x -> unFL $ normalFormWith groundNormalFormFL x
  HaskellVal (x :: b) -> case decomposeInjectivity @FL @a @b of
    Refl -> return (HaskellVal x)
--TODO: Alternatively:
--groundNormalFormFL fl = fl >>= normalFormWith groundNormalFormFL

normalFormFL :: forall a. NormalForm a => FL (Lifted FL a) -> FL (Lifted FL a)
normalFormFL fl = FL $ resolveFL fl >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
      NoPrimitive -> return (Var i)
      Primitive   -> if isUnconstrained i constraintStore
                       then return (Var i)
                       else unFL $ normalFormFL (instantiate i)
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

evalFL :: FL a -> [FLVal a]
evalFL fl = evalND (unFL fl) initFLState

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

class Matchable a where
  match :: Lifted FL a -> a -> FL ()

matchFL :: forall a. (To a, Matchable a) => FL (Lifted FL a) -> a -> FL ()
matchFL fl y = FL $ resolveFL fl >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { heap = insertBinding i (toFL y) heap
                     , .. })
        return (Val ())
      Primitive   ->
        if isUnconstrained i constraintStore
          then do --TODO: fallunterscheidung tauschen. da nur variablen primitiven typs constrained sein können, kann man die unterscheidung von primitive und noprimitive eigentlich weglassen. @Kai: wie siehst du das? andererseits braucht man die primitiveinfo um den kontext zur verfügung zu haben....
            put (FLState { heap = insertBinding i (toFL y) heap
                         , .. })
            return (Val ())
          else
            let c = eqConstraint (Var i) (Val (to y))
                constraintStore' = insertConstraint c [i] constraintStore
            in if isConsistent constraintStore'
                 then do
                   put (FLState { heap = insertBinding i (toFL y) heap
                               , constraintStore = constraintStore'
                               , .. })
                   return (Val ())
                 else empty
  Val x  -> unFL $ match x y
  HaskellVal x -> unFL $ match (to x) y

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
instantiateSameConstructor :: (HasPrimitiveInfo (Lifted FL a), Unifiable a) => Lifted FL a -> ID -> FL ()
instantiateSameConstructor x i = instantiate i >>= lazyUnify x --TODO: discuss why this is inefficient

{-
narrowSame NilFL = NilFL
narrowSame (ConsFL _ _) = ConsFL free free
-}

lazyUnifyVar :: forall a. (Unifiable a, HasPrimitiveInfo (Lifted FL a)) => Lifted FL a -> ID -> FL ()
lazyUnifyVar x i = FL $ get >>= \ FLState { .. } ->
  case primitiveInfo @(Lifted FL a) of
    NoPrimitive -> do
      --TODO: just narrow a single constructor
      unFL $ instantiateSameConstructor x i
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
lazyUnifyFL fl1 fl2 = FL $ resolveFL fl1 >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { heap = insertBinding i fl2 heap
                     , .. })
        return (Val ())
      Primitive   ->
        if isUnconstrained i constraintStore
          then do
            put (FLState { heap = insertBinding i fl2 heap
                         , .. })
            return (Val ())
          else --TODO: i ist constrained, also müssen wir uns den anderen wert anschauen, um zu checken, ob er einem bereits bestehenden constraint widerspricht
            resolveFL fl2 >>= \case
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
  Val x  -> resolveFL fl2 >>= \case
    Var j        -> unFL $ lazyUnifyVar x j
    Val y        -> unFL $ lazyUnify x y
    HaskellVal y -> unFL $ lazyUnify x (to y)
  HaskellVal x -> resolveFL fl2 >>= \case
    Var j        -> unFL $ lazyUnifyVar (to x) j
    Val y        -> unFL $ lazyUnify (to x) y
    HaskellVal y -> unFL $ lazyUnify @a (to x) (to y) --TODO: das wäre im prinzip gleichheit...


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
  toWith _ f = Func $ \x -> toFL' (f (fromFL (groundNormalFormFL x)))
  --toWith _ f = Func $ \x -> FL $ groundNormalFormFL x >>= (unFL . toFL' . f . fromIdentity)
--instance (From a, NormalForm (Lifted FL a), To b) => To (a -> b) where
  --toWith _ f = Func $ \x -> toFL' (f (fromFL (groundNormalFormFL x)))

instance MonadShare m => Shareable m ((-->) m a b) where
  shareArgs = return

appFL :: Monad m => m ((-->) m a b) -> m a -> m b
mf `appFL` x = mf >>= \ (Func f) -> f x

-- This function incorporates the improvement from the paper for
-- partial values in the context of partial inversion with higher-order functions.
toFL' :: To a => a -> FL (Lifted FL a)
toFL' x | isBottom x = empty
        | otherwise  = return (toWith toFL' x)

type Input a = (To a, Unifiable a)
type Output a = (From a, HasPrimitiveInfo (Lifted FL a), NormalForm a)
