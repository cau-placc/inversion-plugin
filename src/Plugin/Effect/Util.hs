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

returnFLF :: (FL a -> FL b) -> FL (a --> b)
returnFLF = return . Func

liftFL1 :: (a -> b) -> FL (a --> b)
liftFL1 f = returnFLF $ \a ->
    a >>= \a' -> returnFL' $ f a'

liftFL2 :: (a -> b -> c) -> FL (a --> b --> c)
liftFL2 f = returnFLF $ \a -> returnFLF $ \b ->
    a >>= \a' -> b >>= \b' -> returnFL' $ f a' b'

assertConstraintND :: Constraint -> [ID] -> ND FLState ()
assertConstraintND c ids = get >>= \FLState { .. } -> put (uncurry (FLState nextID heap) (insertConstraint c ids (constraints, constrainedVars)))

checkConsistencyND :: ND FLState ()
checkConsistencyND = get >>= \FLState {..} -> unless (isConsistent (constraints, constrainedVars)) mzero

freshIdentifierND :: ND FLState ID
freshIdentifierND = get >>= \FLState {..} -> put (FLState (nextID + 1) heap constraints constrainedVars) >> return nextID
