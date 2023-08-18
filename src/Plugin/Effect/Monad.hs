{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
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

import Control.Applicative    (Alternative(..))
import Control.Exception      (Exception, throw, catch)
import Control.Monad.Identity
import Control.Monad.State

import           Data.Kind                    (Type)
import qualified Data.Kind
import           Data.IntMap                  (IntMap)
import qualified Data.IntMap        as IntMap
import           Data.Set                     (Set)
import qualified Data.Set           as Set
import           Data.Typeable                (type (:~:)(..))

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

type ID = Int

--------------------------------------------------------------------------------

data Untyped = forall a. Untyped a

insertBinding :: Functor m => ID -> m a -> IntMap (m Untyped) -> IntMap (m Untyped)
insertBinding i = IntMap.insert i . fmap Untyped

findBinding :: Functor m => ID -> IntMap (m Untyped) -> Maybe (m a)
findBinding i = fmap (fmap (\ (Untyped x) -> unsafeCoerce x)) . IntMap.lookup i

class ShareState m s | s -> m where
  shareID     :: s -> ID
  shareMap    :: s -> IntMap (m Untyped)
  setShareID  :: ID -> s -> s
  setShareMap :: IntMap (m Untyped) -> s -> s

instance (Monad m, ShareState m s, MonadState s m) => MonadShare m where
  share mx = do
    i <- gets shareID
    modify (setShareID (succ i))
    return $ do
      m <- gets shareMap
      case findBinding i m of
        Nothing  -> mx >>= \x -> do
          modify (\s -> setShareMap (insertBinding i (return x) (shareMap s)) s)
          return x
        Just mx' -> mx'

--------------------------------------------------------------------------------

type ND s = StateT s Search

evalND :: ND s a -> s -> [a]
evalND nd s = search (searchTree (evalStateT nd s))
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

freshShareID :: (MonadState s m, ShareState m s, MonadShare m) => m ID
freshShareID = do
  i <- gets shareID
  modify (setShareID (succ i))
  return i

--------------------------------------------------------------------------------

class Instantiatable a where
  instantiate :: [FL a]
  -- TODO: narrowSameConstr :: a -> a

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

initialConstraintStore :: ConstraintStore
initialConstraintStore = ConstraintStore {
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

data PrimitiveInfo a = Instantiatable a => NoPrimitive
                     | Constrainable a => Primitive

class HasPrimitiveInfo a where
  primitiveInfo :: PrimitiveInfo a

--------------------------------------------------------------------------------

data FLVal (a :: Type) where
  Var        :: HasPrimitiveInfo a => ID -> FLVal a
  Val        :: a -> FLVal a
  HaskellVal :: To b => b -> FLVal (Lifted FL b)

--------------------------------------------------------------------------------

data FLState = FLState {
    _shareID        :: ID,
    _shareMap       :: IntMap (FL Untyped),
    varID           :: ID,
    varMap          :: IntMap (FL Untyped),
    constraintStore :: ConstraintStore
  }

instance ShareState FL FLState where
  shareID         = _shareID
  shareMap        = _shareMap
  setShareID i s  = s { _shareID = i }
  setShareMap m s = s { _shareMap = m }

initialFLState :: FLState
initialFLState = FLState {
    _shareID        = 0,
    _shareMap       = IntMap.empty,
    varID           = -1,
    varMap          = IntMap.empty,
    constraintStore = initialConstraintStore
  }

--------------------------------------------------------------------------------

newtype FL a = FL { unFL :: ND FLState (FLVal a) }

evalFL :: FL a -> [FLVal a]
evalFL fl = evalND (unFL fl) initialFLState

instance Functor FL where
  fmap = liftM

instance Applicative FL where
  pure x = FL (pure (Val x))
  (<*>) = ap

dereference :: ND FLState (FLVal a) -> ND FLState (FLVal a)
dereference = go []
  where go is nd = nd >>= \case
          Val x -> return (Val x)
          Var i | i `elem` is -> return (Var i)
                | otherwise   -> get >>= \ FLState { .. } -> case findBinding i varMap of
                                                               Nothing -> return (Var i)
                                                               Just fl -> go (i : is) (unFL fl)
          HaskellVal x -> return (HaskellVal x)

instantiateVar :: forall a. HasPrimitiveInfo a => ID -> ND FLState a
instantiateVar i = case primitiveInfo @a of
  NoPrimitive -> msum (map update instantiate)
    where update (FL ndx) = do
            Val x <- ndx
            modify $ \ FLState { .. } -> FLState { varMap = insertBinding i (return x) varMap, .. }
            return x
  Primitive   -> get >>= \ FLState { .. } -> msum (map update (generate i constraintStore))
    where update x = do
            let c = eqConstraint (Var i) (Val x)
            modify $ \ FLState { .. } -> FLState { varMap = insertBinding i (return x) varMap
                                                 , constraintStore = insertConstraint c [i] constraintStore
                                                 , .. }
            return x

instance Monad FL where
  fl >>= f = FL $ dereference (unFL fl) >>= \case
    Var i        -> instantiateVar i >>= unFL . f
    Val x        -> unFL (f x)
    HaskellVal x -> unFL (f (to x))

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

instance MonadState FLState FL where
  get = FL (Val <$> get)
  put s = FL (Val <$> put s)

freshVarID :: ND FLState ID
freshVarID = do
  i <- gets varID
  modify (\s -> s { varID = pred i })
  return i

free :: HasPrimitiveInfo a => FL a
free = FL (Var <$> freshVarID)

-- TODO: Curry module erstellen

--------------------------------------------------------------------------------


-- TODO: GHC injectivity check cannot do decomposition, https://gitlab.haskell.org/ghc/ghc/-/issues/10833
-- Thus, we create the proof manually using unsafeCoerce
decomposeInjectivity :: Lifted m a ~ Lifted m b => a :~: b
decomposeInjectivity = unsafeCoerce Refl

class NormalForm a where
  normalFormWith :: (forall b. NormalForm b => FL b -> FL b) -> a -> FL a

{-
Without HaskellVals, we could simply write the following.
groundNormalFormFL fl = fl >>= normalFormWith groundNormalFormFL
-}
groundNormalFormFL :: forall a. NormalForm a => FL a -> FL a
groundNormalFormFL fl = FL $ dereference (unFL fl) >>= \case
  Var i -> instantiateVar i >>= unFL . normalFormWith groundNormalFormFL
  Val x -> unFL $ normalFormWith groundNormalFormFL x
  HaskellVal (x :: b) -> case decomposeInjectivity @FL @a @(Lifted FL b) of
    Refl -> return (HaskellVal x)

normalFormFL :: forall a. NormalForm a => FL a -> FL a
normalFormFL fl = FL $ dereference (unFL fl) >>= \case
  Var i -> case primitiveInfo @a of --TODO: eigentlich nicht notwendig, da nicht primitive typen immer unconstrained sind, aber so spart man sich ggf. das nachschlagen und die unterscheidung wird auch hier konsequent umgesetzt.
    NoPrimitive -> return (Var i)
    Primitive   -> get >>= \ FLState { .. } ->
      if isUnconstrained i constraintStore
        then return (Var i)
        else instantiateVar i >>= unFL . normalFormWith normalFormFL
  Val x -> unFL $ normalFormWith normalFormFL x
  HaskellVal (x :: b) -> case decomposeInjectivity @FL @a @(Lifted FL b) of
    Refl -> return (HaskellVal x)

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
   HaskellVal (x :: b) -> case decomposeInjectivity @FL @a @b of
     Refl -> x

fromFL :: From a => FL (Lifted FL a) -> a
fromFL fl = fromFLVal (head (evalFL fl))

--------------------------------------------------------------------------------

class Unifiable a where
  unify :: Lifted FL a -> Lifted FL a -> FL ()
  lazyUnify :: Lifted FL a -> Lifted FL a -> FL ()

unifyFL :: forall a. Unifiable a => FL (Lifted FL a) -> FL (Lifted FL a) -> FL ()
unifyFL fl1 fl2 = FL $ do
  nd1 <- dereference (unFL fl1)
  nd2 <- dereference (unFL fl2)
  FLState { .. } <- get
  case (nd1, nd2) of
    (Var i, Var j)
      | i == j -> return (Val ())
      | otherwise -> case primitiveInfo @(Lifted FL a) of
        NoPrimitive -> do
          put (FLState { varMap = insertBinding i (FL (return nd2)) varMap
                       , .. })
          return (Val ())
        Primitive -> let c = eqConstraint @(Lifted FL a) (Var i) (Var j)
                         constraintStore' = insertConstraint c [i, j] constraintStore
                     in if isUnconstrained i constraintStore || isUnconstrained j constraintStore || isConsistent constraintStore'
                          then do
                            put (FLState { varMap = insertBinding i (FL (return nd2)) varMap
                                         , constraintStore = constraintStore'
                                         , .. })
                            return (Val ())
                          else empty
    (Var i, Val y) -> unifyWithVar y i
    (Val x, Var j) -> unifyWithVar x j
    (Val x, Val y) -> unFL $ unify x y
    (Var i, HaskellVal y) -> unifyWithVar (to y) i
    (Val x, HaskellVal y) -> unFL $ unify x (to y)
    (HaskellVal x, Var j) -> unifyWithVar (to x) j
    (HaskellVal x, Val y) -> unFL $ unify (to x) y
    (HaskellVal x, HaskellVal y) -> unFL $ unify (to x) (to y)

unifyWithVar :: forall a. (Unifiable a, HasPrimitiveInfo (Lifted FL a)) => Lifted FL a -> ID -> ND FLState (FLVal ())
unifyWithVar x i = get >>= \ FLState { .. } ->
  case primitiveInfo @(Lifted FL a) of
    NoPrimitive -> instantiateVar i >>= unFL . unify x --TODO: instantiateVarWithSameConstructor i x anstelle von instantiateVar i
    Primitive -> let c = eqConstraint (Var i) (Val x)
                     constraintStore' = insertConstraint c [i] constraintStore
                 in if isUnconstrained i constraintStore || isConsistent constraintStore'
                      then do
                        put (FLState { varMap = insertBinding i (return x) varMap
                                     , constraintStore = constraintStore'
                                     , .. })
                        return (Val ())
                      else empty --TODO: auslagern

-- output class lohnt sich für: $(inOutClassInv 'sort (Out [| [LT, var 1, GT] |] [| var 1 : var 2 |]))
-- $(inOutClassInv 'sort (Out [| [LT, var 1, GT] |] [| var 2 | ]))

-- $(inOutClassInv 'f (Out [| Just (var 1) |]) [| var 2 |])
-- f (Just x) = not x
-- f Nothing = False

--TODO: check lazyUnifyFL (x, failed) (y,y)
lazyUnifyFL :: forall a. Unifiable a => FL (Lifted FL a) -> FL (Lifted FL a) -> FL ()
lazyUnifyFL fl1 fl2 = FL $ dereference (unFL fl1) >>= \case
  Var i -> get >>= \ FLState { .. } ->
    case primitiveInfo @(Lifted FL a) of
      NoPrimitive -> do
        put (FLState { varMap = insertBinding i fl2 varMap
                     , .. })
        return (Val ())
      Primitive   ->
        if isUnconstrained i constraintStore
          then do
            put (FLState { varMap = insertBinding i fl2 varMap
                         , .. })
            return (Val ())
          else --i ist constrained, also müssen wir uns den anderen wert anschauen, um zu checken, ob er einem bereits bestehenden constraint widerspricht
            dereference (unFL fl2) >>= \case
              Var j -> --TODO: kai: add check if i == j. und außerdem kann es sein, dass j unconstrained ist. dann kann j nichts ändern
                let c = eqConstraint @(Lifted FL a) (Var i) (Var j)
                    constraintStore' = insertConstraint c [i, j] constraintStore
                in if isUnconstrained j constraintStore || isConsistent constraintStore'
                     then do
                       put (FLState { varMap = insertBinding i (FL (return (Var @(Lifted FL a) j))) varMap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
              Val y ->
                let c = eqConstraint (Var i) (Val y)
                    constraintStore' = insertConstraint c [i] constraintStore
                in if isConsistent constraintStore'
                     then do
                       put (FLState { varMap = insertBinding i (return y) varMap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
              HaskellVal y ->
                let y' = to y in
                let c = eqConstraint (Var i) (Val y')
                    constraintStore' = insertConstraint c [i] constraintStore
                in if isConsistent constraintStore'
                     then do
                       put (FLState { varMap = insertBinding i (return y') varMap
                                    , constraintStore = constraintStore'
                                    , .. })
                       return (Val ())
                     else empty
  Val x  -> dereference (unFL fl2) >>= \case
    Var j        -> lazyUnifyWithVar x j
    Val y        -> unFL $ lazyUnify x y
    HaskellVal y -> unFL $ lazyUnify x (to y)
  HaskellVal x -> dereference (unFL fl2) >>= \case
    Var j        -> lazyUnifyWithVar (to x) j
    Val y        -> unFL $ lazyUnify (to x) y
    HaskellVal y -> unFL $ lazyUnify @a (to x) (to y)

lazyUnifyWithVar :: forall a. (Unifiable a, HasPrimitiveInfo (Lifted FL a)) => Lifted FL a -> ID -> ND FLState (FLVal ())
lazyUnifyWithVar x i = get >>= \ FLState { .. } ->
  case primitiveInfo @(Lifted FL a) of
    NoPrimitive -> instantiateVar i >>= unFL . lazyUnify x --TODO: instantiateVarWithSameConstructor i x anstelle von instantiateVar i
    Primitive -> let c = eqConstraint (Var i) (Val x)
                     constraintStore' = insertConstraint c [i] constraintStore
                 in if isUnconstrained i constraintStore || isConsistent constraintStore'
                      then do
                        put (FLState { varMap = insertBinding i (return x) varMap
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
class (From a, To a, Unifiable a, NormalForm (Lifted FL a), HasPrimitiveInfo (Lifted FL a), ShowFree a) => Invertible a

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

instance (From a, NormalForm (Lifted FL a), To b) => To (a -> b) where
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
type Output a = (From a, HasPrimitiveInfo (Lifted FL a), NormalForm (Lifted FL a)) --TODO: Get rid of the tpye family maybe?
--TODO: welche typklassen sind wichtig?
