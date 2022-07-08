{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecordWildCards #-}
module Plugin.Effect.Util where

import Control.Applicative
import Control.Monad
import Control.Monad.State

import Plugin.Effect.Monad
import Plugin.Lifted

returnFLF :: (FL a -> FL b) -> FL (a :--> b)
returnFLF = return . Func

liftFL1 :: (a -> b) -> FL (a :--> b)
liftFL1 f = returnFLF $ \a ->
    a >>= \a' -> return $ f a'

liftFL2 :: (a -> b -> c) -> FL (a :--> b :--> c)
liftFL2 f = returnFLF $ \a -> returnFLF $ \b ->
    a >>= \a' -> b >>= \b' -> return $ f a' b'

--TODO: only use for primitives
liftFL1Convert :: (From a, To b) => (a -> b) -> FL (Lifted FL (a -> b))
liftFL1Convert f = returnFLF $ \a ->
    a >>= \a' -> return $ to (f (unsafeFrom a'))

liftFL2Convert :: (From a, From b, To c) => (a -> b -> c) -> FL (Lifted FL (a -> b -> c))
liftFL2Convert f = returnFLF $ \a -> returnFLF $ \b ->
    a >>= \a' -> b >>= \b' -> return $ to (f (unsafeFrom a') (unsafeFrom b'))

assertConstraintND :: Constraint -> [ID] -> ND FLState ()
assertConstraintND c ids = get >>= \FLState { .. } -> put (FLState nextID heap (insertConstraint c ids constraintStore))

checkConsistencyND :: ND FLState ()
checkConsistencyND = get >>= \FLState {..} -> unless (isConsistent constraintStore) empty

freshIdentifierND :: ND FLState ID
freshIdentifierND = get >>= \FLState {..} -> put (FLState (nextID - 1) heap constraintStore) >> return nextID

apply2FL :: FL ((-->) FL a ((-->) FL b c)) -> FL a -> FL b -> FL c
apply2FL f a b = f `appFL` a `appFL` b

apply3FL :: FL ((-->) FL a ((-->) FL b ((-->) FL c d))) -> FL a -> FL b -> FL c -> FL d
apply3FL f a b c = f `appFL` a `appFL` b `appFL` c

unsafeFrom :: From a => Lifted FL a -> a
unsafeFrom = from
