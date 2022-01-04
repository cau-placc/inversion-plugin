{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
module Plugin.Effect.Util where

import Control.Applicative
import Control.Monad
import Control.Monad.State

import Test.ChasingBottoms.IsBottom

import Plugin.Effect.Monad

returnFL' :: a -> FL a
returnFL' x | isBottom x = empty
            | otherwise  = return x

returnFLF :: (FL a -> FL b) -> FL (a :--> b)
returnFLF = return . Func

liftFL1 :: (a -> b) -> FL (a :--> b)
liftFL1 f = returnFLF $ \a ->
    a >>= \a' -> returnFL' $ f a'

liftFL2 :: (a -> b -> c) -> FL (a :--> b :--> c)
liftFL2 f = returnFLF $ \a -> returnFLF $ \b ->
    a >>= \a' -> b >>= \b' -> returnFL' $ f a' b'

liftFL1Convert :: (Convertible a, Convertible b) => (a -> b) -> FL (Lifted FL (a -> b))
liftFL1Convert f = returnFLF $ \a ->
    a >>= \a' -> returnFL' $ to (f (from a'))

liftFL2Convert :: (Convertible a, Convertible b, Convertible c) => (a -> b -> c) -> FL (Lifted FL (a -> b -> c))
liftFL2Convert f = returnFLF $ \a -> returnFLF $ \b ->
    a >>= \a' -> b >>= \b' -> returnFL' $ to (f (from a') (from b'))

assertConstraintND :: Constraint -> [ID] -> ND FLState ()
assertConstraintND c ids = get >>= \FLState { .. } -> put (uncurry (FLState nextID heap) (insertConstraint c ids (constraints, constrainedVars)))

checkConsistencyND :: ND FLState ()
checkConsistencyND = get >>= \FLState {..} -> unless (isConsistent (constraints, constrainedVars)) mzero

freshIdentifierND :: ND FLState ID
freshIdentifierND = get >>= \FLState {..} -> put (FLState (nextID + 1) heap constraints constrainedVars) >> return nextID

apply2FL :: FL ((-->) FL a ((-->) FL b c)) -> FL a -> FL b -> FL c
apply2FL f a b = f `appFL` a `appFL` b

apply3FL :: FL ((-->) FL a ((-->) FL b ((-->) FL c d))) -> FL a -> FL b -> FL c -> FL d
apply3FL f a b c = f `appFL` a `appFL` b `appFL` c