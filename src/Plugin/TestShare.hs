{-# LANGUAGE RecursiveDo, ExistentialQuantification, BangPatterns, LambdaCase, FlexibleInstances #-}
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
module Plugin.TestShare where

import Control.Monad.State
import Control.Applicative
import qualified Data.Map as Map
import Unsafe.Coerce
import Plugin.Effect.Tree


type Heap = Map.Map Int Untyped

data Untyped = forall a. Untyped a

class Monad m => MonadShare m where
  share :: Shareable m a => m a -> m (m a)

class Shareable m a where
  shareArgs :: a -> m a

instance MonadShare m => Shareable m Bool where
  shareArgs !x = return x

data ListM m a = NilM | ConsM (m a) (m (ListM m a))

instance (MonadShare m, Shareable m a) => Shareable m (ListM m a) where
  shareArgs NilM = return NilM
  shareArgs (ConsM x xs) = ConsM <$> share x <*> share xs

instance MonadShare SC where
  share act' = memo (act' >>= shareArgs)
    where memo act = do
            St i aa <- SC $ (fmap Val get)
            SC (Val <$> put (St (succ i) aa))
            return $ do
              St _ h <- SC $ (fmap Val get)
              case Map.lookup i h of
                Nothing -> do
                  x <- act
                  ~(St k h2) <- SC $ (fmap Val get)
                  SC (Val <$> put (St k (Map.insert i (Untyped x) h2)))
                  return x
                Just (Untyped x) -> return (unsafeCoerce x)

data St = St Int Heap

data FLVal a = Var Int | Val a
  deriving Show

newtype SC a = SC (StateT St Search (FLVal a))

instance Functor SC where
  fmap = liftM

instance Applicative SC where
  pure x = SC (pure (Val x))
  (<*>) = ap

instance Monad SC where
  (SC fl) >>= f = SC $ fl >>= (\(SC s) -> s) . \case
    Var i        -> error ""
    Val x        -> f x

instance Alternative SC where
  empty = SC empty
  SC a1 <|> SC a2 = SC (a1 <|> a2)

instance MonadPlus SC

instance MonadFail SC where
  fail s = SC (fail s)

instance MonadFix SC where
  mfix f = SC $ mfix ((\(SC s) -> s) . f . unVal)
    where
      unVal (Val x) = x
      unVal _ = error "Not a Val in mfix"

(?) :: a -> a -> a
(?) = const

originalTest :: [Bool]
originalTest = let x = (False?True) : x
                   y = (False?True) : y
    in x

test :: SC (ListM SC Bool)
test = do
  (x, _) <- mfix (\(~(x', y')) -> (,) <$> share (return (ConsM (return False <|> return True) y'))
                                      <*> share (return (ConsM (return False <|> return True) x')))
  x

testTake :: SC (ListM SC Bool) -> SC (SC Bool, SC Bool, SC Bool)
testTake xs = xs >>= \case
  ConsM y ys -> ys >>= \case
    ConsM z zs -> zs >>= \case
     ConsM a as -> return (y, z, a)

nf :: SC (SC Bool, SC Bool, SC Bool) -> SC (Bool, Bool, Bool)
nf x = x >>= \case
  (x, y, a) -> (,,) <$> x <*> y <*> a

run :: SearchTree (FLVal (Bool, Bool, Bool))
run = searchTree $ evalStateT ((\(SC s) -> s) (nf (testTake test))) (St 0 mempty)
