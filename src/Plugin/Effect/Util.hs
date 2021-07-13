{-# LANGUAGE TypeOperators #-}
module Plugin.Effect.Util where

import Control.Monad
import Control.Monad.State

import Test.ChasingBottoms.IsBottom

import Plugin.Effect.Monad

returnFL' :: a -> FL a
returnFL' x | isBottom x = failedFL
            | otherwise  = returnFL x

returnFLF :: (FL a -> FL b) -> FL (a --> b)
returnFLF = returnFL . Func

liftFL1 :: (a -> b) -> FL (a --> b)
liftFL1 f = returnFLF $ \a ->
    a >>= \a' -> returnFL' $ f a'

liftFL2 :: (a -> b -> c) -> FL (a --> b --> c)
liftFL2 f = returnFLF $ \a -> returnFLF $ \b ->
    a >>= \a' -> b >>= \b' -> returnFL' $ f a' b'

assertConstraintND :: Constraint -> ND ()
assertConstraintND c = lift get >>= \(j, h, cst) -> lift (put (j, h, insertConstraint c cst))

checkConsistencyND :: ND ()
checkConsistencyND = lift get >>= \(_, _, cst) -> unless (isConsistent cst) mzero

freshIdentifierND :: ND ID
freshIdentifierND = lift get >>= \(j, h, cst) -> lift (put (j + 1, h, cst)) >> return j
