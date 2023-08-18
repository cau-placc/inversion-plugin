{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MagicHash                #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE NoStarIsType             #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE QuantifiedConstraints    #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE RecordWildCards          #-}
{-# LANGUAGE ScopedTypeVariables      #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE TypeFamilies             #-}
{-# LANGUAGE TypeOperators            #-}
{-# LANGUAGE UnboxedTuples            #-}
{-# LANGUAGE UndecidableInstances     #-}
{-# LANGUAGE NoMonoLocalBinds         #-}

{-# OPTIONS_GHC -Wno-orphans              #-}
{-# OPTIONS_GHC -Wno-unused-foralls       #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use newtype instead of data" #-}
{-# HLINT ignore "Use >=>" #-}
{-# HLINT ignore "Reduce duplication" #-}

-- |
-- Module      : Plugin.InversionPlugin.BuiltIn
-- Description : Built-In functions, types and type classes
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- License     : BSD-3 Clause
-- Maintainer  : kai.prott@hotmail.de
--
-- This module contains lifted replacements for data types, functions
-- and type classes for Haskell's default Prelude.
-- This module is not supposed to be imported by users, please import
-- 'Plugin.InversionPlugin.Prelude' instead.
module Plugin.BuiltIn where

import qualified Control.Monad as P
import qualified GHC.Base      as P hiding (mapM)
import qualified GHC.Real      as P
import qualified GHC.Exts      as P
import qualified Prelude       as P hiding (mapM)
import           GHC.Types (RuntimeRep, Type, Multiplicity)
import           GHC.Int   (Int(..))
import           Unsafe.Coerce ( unsafeCoerce )
import           Prelude ( Bool (..), Double, Float, Integer, Ordering (..), ($) )
import           Plugin.BuiltIn.Primitive
import           Plugin.Effect.Monad as M
import           Plugin.Effect.TH
import           Plugin.Effect.Util  as M
import           Plugin.Lifted
import           Plugin.Trans.TysWiredIn
import           Data.Tuple.Solo

-- * Lifted unrestricted function type
type (:--->#) (m :: Type -> Type) (mult :: Multiplicity) (r1 :: RuntimeRep) (r2 :: RuntimeRep) = (-->) m

-- * Lifted restricted function type
type (:--->) (m :: Type -> Type) (r1 :: RuntimeRep) (r2 :: RuntimeRep) = (-->) m

-- * Lifted tuple types and internal instances

data SoloFL (m :: Type -> Type) a = SoloFL (m a)

type instance Lifted m Solo = SoloFL m
type instance Lifted m (Solo a) = SoloFL m (Lifted m a)

instance HasPrimitiveInfo a => HasPrimitiveInfo (SoloFL FL a) where
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo a => Instantiatable (SoloFL FL a) where
  instantiate = [SoloFL P.<$> share free]

instance To a => To (Solo a) where
  toWith tf (Solo x) = SoloFL (tf x)

instance From a => From (Solo a) where
  from (SoloFL x) = Solo (fromFL x)

instance Unifiable a => Unifiable (Solo a) where
  unify (SoloFL x) (SoloFL y) = unifyFL x y
  lazyUnify (SoloFL x) (SoloFL y) = lazyUnifyFL x y

instance NormalForm a => NormalForm (Solo a) where
  normalFormWith nf = \case
    SoloFL x -> FL $
      unFL (nf x) P.>>= \y ->
        unFL (P.return (SoloFL (FL (P.return y))))

instance ShowFree a => ShowFree (Solo a) where
  showsFreePrec' d (Solo x) = P.showParen (d P.> 10) $
    P.showString "Solo " P.. showsFreePrec 11 x

instance Invertible a => Invertible (Solo a)

data Tuple2FL (m :: Type -> Type) a b = Tuple2FL (m a) (m b)

type instance Lifted m (,) = Tuple2FL m
type instance Lifted m ((,) a) = Tuple2FL m (Lifted m a)
type instance Lifted m (a, b) = Tuple2FL m (Lifted m a) (Lifted m b)

instance (HasPrimitiveInfo a, HasPrimitiveInfo b) => HasPrimitiveInfo (Tuple2FL FL a b) where
  primitiveInfo = NoPrimitive

instance (HasPrimitiveInfo a, HasPrimitiveInfo b) => Instantiatable (Tuple2FL FL a b) where
  instantiate = [Tuple2FL P.<$> share free P.<*> share free]

instance (To a, To b) => To (a, b) where
  toWith tf (x1, x2) = Tuple2FL (tf x1) (tf x2)

instance (From a, From b) => From (a, b) where
  from (Tuple2FL x1 x2) = (fromFL x1, fromFL x2)

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where
  unify (Tuple2FL x1 x2) (Tuple2FL y1 y2) = unifyFL x1 y1 P.>> unifyFL x2 y2
  lazyUnify (Tuple2FL x1 x2) (Tuple2FL y1 y2) = lazyUnifyFL x1 y1 P.>> lazyUnifyFL x2 y2

{-instance (NormalForm a, NormalForm b) => NormalForm (a, b) where
  normalFormWith nf = \case
    Tuple2FL x1 x2 ->
      nf x1 P.>>= \y1 ->
        nf x2 P.>>= \y2 ->
        P.return (Result (P.pure (Tuple2FL y1 y2)))-}
instance (NormalForm a, NormalForm b) => NormalForm (a, b) where
  normalFormWith nf = \case
    Tuple2FL x1 x2 -> FL $
      unFL (nf x1) P.>>= \y1 ->
        unFL(nf x2) P.>>= \y2 ->
          unFL (P.return (Tuple2FL (FL (P.return y1)) (FL (P.return y2))))
-- instance (NormalForm a, NormalForm b) => NormalForm (Tuple2FL FL a b) where
--   normalFormWith nf = \case
--     Tuple2FL x1 x2 ->
--       nf x1 P.>>= \y1 ->
--         nf x2 P.>>= \y2 ->
--           P.return (Tuple2FL (P.return y1) (P.return y2))

instance (ShowFree a, ShowFree b) => ShowFree (a, b) where
  showsFreePrec' _ (x1, x2) = P.showString "(" P.. showsFree x1 P.. P.showString "," P.. showsFree x2 P.. P.showString ")"

instance (Invertible a, Invertible b) => Invertible (a, b)

P.concat P.<$> P.mapM genLiftedTupleDataDeclAndInstances [3 .. maxTupleArity]

-- * Lifted list type and internal instances

data ListFL (m :: Type -> Type) a = NilFL | ConsFL (m a) (m (ListFL m a))

type StringFL m = ListFL m (CharFL m)

type instance Lifted m [] = ListFL m
type instance Lifted m [a] = ListFL m (Lifted m a)

instance HasPrimitiveInfo a => HasPrimitiveInfo (ListFL FL a) where
  primitiveInfo = NoPrimitive

instance (HasPrimitiveInfo a, HasPrimitiveInfo (ListFL FL a)) => Instantiatable (ListFL FL a) where
  instantiate = [P.return NilFL, ConsFL P.<$> share free P.<*> share free]

instance (To a, To [a]) => To [a] where
  toWith _  [] = NilFL
  toWith tf (x : xs) = ConsFL (tf x) (tf xs)

instance (From a, From [a]) => From [a] where
  from NilFL = []
  from (ConsFL x xs) = fromFL x : fromFL xs

instance (Unifiable a, Unifiable [a]) => Unifiable [a] where
  unify NilFL NilFL = P.return ()
  unify (ConsFL x xs) (ConsFL y ys) = unifyFL x y P.>> unifyFL xs ys
  unify _ _ = P.empty
  lazyUnify NilFL NilFL = P.return ()
  lazyUnify (ConsFL x xs) (ConsFL y ys) = lazyUnifyFL x y P.>> lazyUnifyFL xs ys
  lazyUnify _ _ = P.empty

instance (NormalForm a, NormalForm [a]) => NormalForm [a] where
  normalFormWith nf = \case
    NilFL -> P.return NilFL
    ConsFL x xs -> FL $
      unFL (nf x) P.>>= \y ->
        unFL (nf xs) P.>>= \ys ->
          unFL (P.return (ConsFL (FL (P.return y)) (FL (P.return ys))))

instance (ShowFree a, ShowFree [a]) => ShowFree [a] where
  showsFreePrec' _ []     = P.showString "[]"
  showsFreePrec' d (x:xs) = P.showParen (d P.> 5) $
    showsFreePrec 6 x P..
    P.showString " : " P..
    showsFreePrec 6 xs

instance Invertible a => Invertible [a]

instance FunctorFL (MaybeFL FL) where
  fmapFL = returnFLF $ \f -> returnFLF $ \x -> x P.>>= \case
    NothingFL -> P.return NothingFL
    JustFL y -> P.return (JustFL (f `appFL` y))

instance ApplicativeFL (MaybeFL FL) where
  pureFL = returnFLF $ \x -> P.return (JustFL x)
  (<*>#) = returnFLF $ \x -> returnFLF $ \y -> x P.>>= \case
    NothingFL -> P.return NothingFL
    JustFL f -> y P.>>= \case
      NothingFL -> P.return NothingFL
      JustFL z -> P.return (JustFL (f `appFL` z))

instance MonadFL (MaybeFL FL) where
  (>>=#) = returnFLF $ \x -> returnFLF $ \f -> x P.>>= \case
    NothingFL -> P.return NothingFL
    JustFL y -> f `appFL` y

-- * Lifted Maybe type and internal instances

data MaybeFL (m :: Type -> Type) a = NothingFL | JustFL (m a)

type instance Lifted m P.Maybe = MaybeFL m
type instance Lifted m (P.Maybe a) = MaybeFL m (Lifted m a)

instance HasPrimitiveInfo a => HasPrimitiveInfo (MaybeFL FL a) where
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo a => Instantiatable (MaybeFL FL a) where
  instantiate = [P.return NothingFL, JustFL P.<$> share free]

instance To a => To (P.Maybe a) where
  toWith _  P.Nothing = NothingFL
  toWith tf (P.Just x) = JustFL (tf x)

instance From a => From (P.Maybe a) where
  from NothingFL = P.Nothing
  from (JustFL x) = P.Just (fromFL x)

instance Unifiable a => Unifiable (P.Maybe a) where
  unify NothingFL NothingFL = P.return ()
  unify (JustFL x) (JustFL y) = unifyFL x y
  unify _ _ = P.empty
  lazyUnify NothingFL NothingFL = P.return ()
  lazyUnify (JustFL x) (JustFL y) = lazyUnifyFL x y
  lazyUnify _ _ = P.empty

instance NormalForm a => NormalForm (P.Maybe a) where
  normalFormWith nf = \case
      NothingFL -> P.return NothingFL
      JustFL x -> FL $
        unFL (nf x) P.>>= \y ->
          unFL (P.return (JustFL (FL (P.return y))))

instance ShowFree a => ShowFree (P.Maybe a) where
  showsFreePrec' _ P.Nothing  = P.showString "Nothing"
  showsFreePrec' d (P.Just x) = P.showParen (d P.> 10) $
    P.showString "Just " P.. showsFreePrec 11 x

instance Invertible a => Invertible (P.Maybe a)

data RatioFL m a = m a :%# m a

type instance Lifted m P.Ratio = RatioFL m
type instance Lifted m (P.Ratio a) = RatioFL m (Lifted m a)

instance HasPrimitiveInfo a => HasPrimitiveInfo (RatioFL FL a) where
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo a => Instantiatable (RatioFL FL a) where
  instantiate = [(:%#) P.<$> share free P.<*> share free]

instance To a => To (P.Ratio a) where
  toWith tf (a P.:% b) = tf a :%# tf b

instance From a => From (P.Ratio a) where
  from (a :%# b) = fromFL a P.:% fromFL b

instance Unifiable a => Unifiable (P.Ratio a) where
  unify (a :%# b) (x :%# y) = unifyFL a x P.>> unifyFL b y
  lazyUnify (a :%# b) (x :%# y) = lazyUnifyFL a x P.>> lazyUnifyFL b y

instance NormalForm a => NormalForm (P.Ratio a) where
  normalFormWith nf = \case
      a :%# b -> FL $
        unFL (nf a) P.>>= \x ->
          unFL (nf b) P.>>= \y ->
            unFL (P.return (FL (P.return x) :%# FL (P.return y)))

instance ShowFree a => ShowFree (P.Ratio a) where
  showsFreePrec' d (x P.:% y) = P.showParen (d P.> 7) $
    showsFreePrec 8 x P.. P.showString " % " P.. showsFreePrec 8 y

instance Invertible a => Invertible (P.Ratio a)

type RationalFL m = RatioFL m (IntegerFL m)

-- * For plugin purposes only.

failFLStr :: P.String -> a
failFLStr = P.error

failFLStrFL :: FL (StringFL FL :--> a)
failFLStrFL = P.return $ Func $ P.const P.empty

-- Lifted seq operator to force evaluation. Forces the effect and value.
seq :: forall (k :: RuntimeRep) a b. a -> b -> b
seq = P.seq

seqFL :: forall (k :: RuntimeRep) a b. FL (a :--> b :--> b)
seqFL = returnFLF $ \a -> returnFLF $ \b ->
  a P.>>= \a' -> P.seq a' b

seqValue :: FL a -> FL b -> FL b
seqValue a b = a P.>>= \a' -> a' `seq` b

-- | Lifted coercion function to replace coercion in newtype-derived instances
-- We need to introduce this unused dummy k,
-- because we replace Data.Coerce.coerce (which has this k).
coerce :: forall (k :: RuntimeRep) a b. a -> b
coerce = unsafeCoerce

coerceFL :: forall (k :: RuntimeRep) a b. FL (a :--> b)
coerceFL = returnFLF $ \(FL a) -> FL $ a P.>>= unsafeCoerce

-- | Lifted equality test for strings
eqString :: P.String -> P.String -> Bool
eqString = (P.==)

-- | Lifted equality test for strings
eqStringFL :: FL (StringFL FL :--> StringFL FL :--> BoolFL FL)
eqStringFL = (==#)

-- | Lifted equality test for characters
eqChar :: P.Char -> P.Char -> Bool
eqChar = (P.==)

-- | Lifted equality test for strings
eqCharFL :: FL (CharFL FL :--> CharFL FL :--> BoolFL FL)
eqCharFL = (==#)

(<##) :: FL (IntFL FL :--> IntFL FL :--> IntFL FL)
(<##) = liftFL2Convert op
  where
    op (I# i1) (I# i2) = I# (i1 P.<# i2)

(==##) :: FL (IntFL FL :--> IntFL FL :--> IntFL FL)
(==##) = liftFL2Convert op
  where
    op (I# i1) (I# i2) = I# (i1 P.==# i2)

-- * Prelude stuff

fstFL :: forall a b. FL (Tuple2FL FL a b :--> a)
fstFL = returnFLF $ \x -> x P.>>= \case
  Tuple2FL a _ -> a

sndFL :: forall a b. FL (Tuple2FL FL a b :--> b)
sndFL = returnFLF $ \x -> x P.>>= \case
  Tuple2FL _ b -> b

undefinedFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . FL a
undefinedFL = P.empty

errorFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . FL (StringFL FL :--> a)
errorFL = failFLStrFL

-- Lifted function to desugar left sections.
leftSectionFL :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep)
                        (n :: Multiplicity) a b.
                 FL ((a :--> b) :--> a :--> b)
leftSectionFL = returnFLF $ \f -> returnFLF $ \a ->
  f `appFL` a

-- Lifted function to desugar right sections.
rightSectionFL :: forall (r1 :: RuntimeRep) (r2 :: RuntimeRep) (r3 :: RuntimeRep)
                         (n1 :: Multiplicity) (n2 :: Multiplicity) a b c.
                  FL ((a :--> b :--> c) :--> b :--> a :--> c)
rightSectionFL = returnFLF $ \f -> returnFLF $ \b -> returnFLF $ \a ->
  f `appFL` a `appFL` b

notFL :: FL (BoolFL FL :--> BoolFL FL)
notFL = liftFL1Convert P.not

idFL :: FL (a :--> a)
idFL = returnFLF P.id

(.#) :: forall a b c. FL ((b :--> c) :--> (a :--> b) :--> a :--> c)
(.#) = returnFLF $ \f -> returnFLF $ \g -> returnFLF $ \a ->
  f `appFL` (g `appFL` a)

flipFL :: forall a b c. FL ((a :--> b :--> c) :--> b :--> a :--> c)
flipFL = returnFLF $ \f -> returnFLF $ \x -> returnFLF $ \y ->
  f `appFL` y `appFL` x

curryFL :: forall a b c. FL ((Tuple2FL FL a b :--> c) :--> a :--> b :--> c)
curryFL = returnFLF $ \f -> returnFLF $ \x -> returnFLF $ \y ->
  f `appFL` P.return (Tuple2FL x y)

uncurryFL :: forall a b c. FL ((a :--> b :--> c) :--> Tuple2FL FL a b :--> c)
uncurryFL = returnFLF $ \f -> returnFLF $ \p ->
  p P.>>= \case
    Tuple2FL x y -> f `appFL` x `appFL` y

-- | Lifted const function
constFL :: FL (a :--> b :--> a)
constFL = returnFLF $ \a -> returnFLF $ P.const a

-- | Lifted logical and
(&&#) :: FL (BoolFL FL :--> BoolFL FL :--> BoolFL FL)
(&&#) = returnFLF $ \a -> returnFLF $ \b -> a P.>>= \case
  FalseFL -> P.return FalseFL
  TrueFL  -> b

-- | Lifted logical and
(||#) :: FL (BoolFL FL :--> BoolFL FL :--> BoolFL FL)
(||#) = returnFLF $ \a -> returnFLF $ \b -> a P.>>= \case
  FalseFL -> b
  TrueFL  -> P.return TrueFL

-- | Lifted otherwise
otherwiseFL :: FL (BoolFL FL)
otherwiseFL = P.return TrueFL

-- | Lifted head function
headFL :: FL (ListFL FL a :--> a)
headFL = returnFLF $ \xs -> xs P.>>= \case
  NilFL -> P.empty
  ConsFL x _ -> x

-- | Lifted tail function
tailFL :: FL (ListFL FL a :--> ListFL FL a)
tailFL = returnFLF $ \xs -> xs P.>>= \case
  NilFL -> P.empty
  ConsFL _ ys -> ys

-- | Lifted (++) function
(++#) :: FL (ListFL FL a :--> ListFL FL a :--> ListFL FL a)
(++#) = returnFLF $ \xs -> returnFLF $ \ys ->
  xs P.>>= \case
    NilFL -> ys
    ConsFL a as -> P.return (ConsFL a ((++#) `appFL` as `appFL` ys))


appendListNoShare :: FL (ListFL FL a :--> ListFL FL a :--> ListFL FL a)
appendListNoShare = returnFLF $ \xs -> returnFLF $ \ys ->
  xs P.>>= \case
    NilFL -> ys
    ConsFL a as -> P.return (ConsFL a (appendListNoShare `appFL` as `appFL` ys))

-- | Lifted reverse function
reverseFL :: FL (ListFL FL a :--> ListFL FL a)
reverseFL = foldlFL `appFL` (flipFL `appFL` returnFLF (\x -> returnFLF $ \xs -> P.return (ConsFL x xs))) `appFL` P.return NilFL

-- | Lifted map function for lists
mapFL :: forall a b. FL ((a :--> b) :--> ListFL FL a :--> ListFL FL b)
mapFL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> P.return (ConsFL (f `appFL` a) (mapFL `appFL` f `appFL` as))

-- | Lifted map function for lists
mapFLNoShare :: FL ((a :--> b) :--> ListFL FL a :--> ListFL FL b)
mapFLNoShare = returnFLF $ \f -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> P.return (ConsFL (f `appFL` a) (mapFLNoShare `appFL` f `appFL` as))

-- | Lifted concat function
concatFL :: forall t a. FoldableFL t
         => FL (t (ListFL FL a) :--> ListFL FL a)
concatFL = foldrFL `appFL` (++#) `appFL` P.return NilFL

-- | Lifted concatMap function
concatMapFL :: forall t a b. FoldableFL t
            => FL ((a :--> ListFL FL b) :--> t a :--> ListFL FL b)
concatMapFL = returnFLF $ \f -> foldrFL `appFL` ((.#) `appFL` (++#) `appFL` f) `appFL` P.return NilFL

-- | Lifted takeWhile function for lists
takeWhileFL :: FL ((a :--> BoolFL FL) :--> ListFL FL a :--> ListFL FL a)
takeWhileFL = returnFLF $ \p' -> share p' P.>>= \p -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> (p `appFL` a) P.>>= \case
      FalseFL -> P.return NilFL
      TrueFL -> P.return (ConsFL a (takeWhileFL `appFL` p `appFL` as))

-- | Lifted dropWhile function for lists
dropWhileFL :: FL ((a :--> BoolFL FL) :--> ListFL FL a :--> ListFL FL a)
dropWhileFL = returnFLF $ \p' -> share p' P.>>= \p -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> (p `appFL` a) P.>>= \case
      FalseFL -> P.return (ConsFL a as)
      TrueFL -> dropWhileFL `appFL` p `appFL` as

-- | Lifted replicate function
replicateFL :: FL (IntFL FL :--> a :--> ListFL FL a)
replicateFL = returnFLF $ \n' -> share n' P.>>= \n -> returnFLF $ \x' -> share x' P.>>= \x ->
  ((==#) `appFL` n `appFL` P.return (IntFL 0)) P.>>= \case
  FalseFL -> ((>#) `appFL` n `appFL` P.return (IntFL 0)) P.>>= \case
    FalseFL -> P.empty
    TrueFL -> P.return (ConsFL x (replicateFL `appFL` ((-#) `appFL` n `appFL` P.return (IntFL 1)) `appFL` x))
  TrueFL -> P.return NilFL

-- | Lifted take function for lists
takeFL :: FL (IntFL FL :--> ListFL FL a :--> ListFL FL a)
takeFL = returnFLF $ \n' -> share n' P.>>= \n -> returnFLF $ \xs ->
  (<=#) `appFL` n `appFL` P.return (IntFL 0) P.>>= \case
    FalseFL -> xs P.>>= \case
      NilFL -> P.return NilFL
      ConsFL a as -> P.return (ConsFL a (takeFL `appFL` ((-#) `appFL` n `appFL` P.return (IntFL 1)) `appFL` as))
    TrueFL -> P.return NilFL

-- | Lifted drop function for lists
dropFL :: FL (IntFL FL :--> ListFL FL a :--> ListFL FL a)
dropFL = returnFLF $ \n' -> share n' P.>>= \n -> returnFLF $ \xs ->
  (<=#) `appFL` n `appFL` P.return (IntFL 0) P.>>= \case
    FalseFL -> xs P.>>= \case
      NilFL -> P.return NilFL
      ConsFL _ as -> dropFL `appFL` ((-#) `appFL` n `appFL` P.return (IntFL 1)) `appFL` as
    TrueFL -> xs

-- | Lifted maybe function
maybeFL :: forall b a. FL (b :--> (a :--> b) :--> MaybeFL FL a :--> b)
maybeFL = returnFLF $ \n -> returnFLF $ \j -> returnFLF $ \m -> m P.>>= \case
  NothingFL -> n
  JustFL x -> j `appFL` x

-- | Lifted lookup function
lookupFL :: forall a b. EqFL a
         => FL (a :--> ListFL FL (Tuple2FL FL a b) :--> MaybeFL FL b)
lookupFL = returnFLF $ \k' -> share k' P.>>= \k -> returnFLF $ \xs -> xs P.>>= \case
  NilFL -> P.return NothingFL
  ConsFL y kvs -> y P.>>= \case
    Tuple2FL k2 v -> ((==#) `appFL` k `appFL` k2) P.>>= \case
      FalseFL -> lookupFL `appFL` k `appFL` kvs
      TrueFL -> P.return (JustFL v)

-- | Lifted notElem function
notElemFL :: forall t a. (FoldableFL t, EqFL a)
           => FL (a :--> t a :--> BoolFL FL)
notElemFL = returnFLF $ \x -> (.#) `appFL` notFL `appFL` (elemFL `appFL` x)

--TODO: Move
data NonEmptyFL a = a :|# [a]
--TODO: Eq, Ord, Functor, Applicative, Monad

--TODO: Move
class SemigroupFL a where
  (<>#) :: FL (a :--> a :--> a)

  sconcat :: FL (NonEmptyFL a :--> a)
  {-sconcat (a :| as) = go a as where
    go b (c:cs) = b <> go c cs
    go b []     = b-}

  stimes :: forall b. IntegralFL b => FL (b :--> a :--> a)
  --stimes = stimesDefault

instance SemigroupFL (ListFL FL a) where
  (<>#) = appendListNoShare
  --stimesFL = stimesListFL

--TODO: Move
class SemigroupFL a => MonoidFL a where
  memptyFL  :: FL a

  mappendFL :: FL (a :--> a :--> a)
  mappendFL = (<>#)

  -- we can only do this because we know that Shareable for Anything is just return.
  mconcatFL :: FL (ListFL FL a :--> a)
  mconcatFL = foldrFL `appFL` mappendFL `appFL` memptyFL

instance MonoidFL (ListFL FL a) where
  memptyFL = P.return NilFL

--TODO: Move to BuiltIn.Foldable
class FoldableFL t where
    foldFL :: MonoidFL m => FL (t m :--> m)
    foldFL = foldMapFL `appFL` idFL

    foldMapFL :: forall a m. MonoidFL m => FL ((a :--> m) :--> t a :--> m)
    foldMapFL = returnFLF $ \f' -> share f' P.>>= \f -> foldrFL `appFL` ((.#) `appFL` mappendFL `appFL` f) `appFL` memptyFL

    foldMap'FL :: forall a m. MonoidFL m => FL ((a :--> m) :--> t a :--> m)
    foldMap'FL = returnFLF $ \f' -> share f' P.>>= \f -> foldl'FL `appFL` returnFLF (\acc -> returnFLF $ \a -> (<>#) `appFL` acc `appFL` (f `appFL` a)) `appFL` memptyFL

    foldrFL :: forall a b. FL ((a :--> b :--> b) :--> b :--> t a :--> b)
    --foldrFL f z t = appEndo (foldMap (Endo #. f) t) z

    foldr'FL :: forall a b. FL ((a :--> b :--> b) :--> b :--> t a :--> b)
    --foldr' f z0 xs = foldl f' id xs z0
    --  where f' k x z = k $! f x z

    foldlFL :: forall a b. FL ((b :--> a :--> b) :--> b :--> t a :--> b)
    --foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

    foldl'FL :: forall a b. FL ((b :--> a :--> b) :--> b :--> t a :--> b)

    foldr1FL :: forall a. FL ((a :--> a :--> a) :--> t a :--> a)
    --foldr1FL f xs = fromMaybe (errorWithoutStackTrace "foldr1: empty structure")
    --                (foldr mf Nothing xs)
    --  where
    --    mf x m = Just (case m of
    --                     Nothing -> x
    --                     Just y  -> f x y)

    foldl1FL :: FL ((a :--> a :--> a) :--> t a :--> a)
    {-foldl1 f xs = fromMaybe (errorWithoutStackTrace "foldl1: empty structure")
                    (foldl mf Nothing xs)
      where
        mf m y = Just (case m of
                         Nothing -> y
                         Just x  -> f x y)-}

    toListFL :: FL (t a :--> ListFL FL a)
    --toList t = build (\ c n -> foldr c n t)

    nullFL :: FL (t a :--> BoolFL FL)
    --null = foldr (\_ _ -> False) True

    lengthFL :: FL (t a :--> IntFL FL)
    --length = foldl' (\c _ -> c+1) 0

    elemFL :: EqFL a => FL (a :--> t a :--> BoolFL FL)
    --elem = any . (==)


    maximumFL :: OrdFL a => FL (t a :--> a)
    {-maximum = fromMaybe (errorWithoutStackTrace "maximum: empty structure") .
       getMax . foldMap' (Max #. (Just :: a -> Maybe a))
    {-# INLINEABLE maximum #-}-}

    minimumFL :: OrdFL a => FL (t a :--> a)
    {-minimumFL = fromMaybe (errorWithoutStackTrace "minimum: empty structure") .
       getMin . foldMap' (Min #. (Just :: a -> Maybe a))
    {-# INLINEABLE minimum #-}-}

    sumFL :: NumFL a => FL (t a :--> a)
    --sum = getSum #. foldMap' Sum

    productFL :: NumFL a => FL (t a :--> a)
    --product = getProduct #. foldMap' Product

instance FoldableFL (ListFL FL) where
  elemFL = returnFLF $ \x' -> share x' P.>>= \x -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.return FalseFL
    ConsFL y ys -> ((==#) `appFL` x `appFL` y) P.>>= \case
      FalseFL -> elemFL `appFL` x `appFL` ys
      TrueFL -> P.return TrueFL
  foldlFL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \e -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> e
    ConsFL y ys -> foldlFL `appFL` f `appFL` (f `appFL` e `appFL` y) `appFL` ys
  foldl1FL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.empty
    ConsFL y ys -> foldlFL `appFL` f `appFL` y `appFL` ys
  foldl'FL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \z -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> z
    ConsFL y ys -> share (f `appFL` z `appFL` y) P.>>= \z' -> seqFL `appFL` z' `appFL` (foldl'FL `appFL` f `appFL` z' `appFL` ys)
  foldrFL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \e -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> e
    ConsFL y ys -> f `appFL` y `appFL` (foldrFL `appFL` f `appFL` e `appFL` ys)
  foldr1FL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.empty
    ConsFL y ys -> ys P.>>= \case
      NilFL -> y
      zs -> f `appFL` y `appFL` (foldr1FL `appFL` f `appFL` P.return zs)
  lengthFL = returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.return (IntFL 0)
    ConsFL _ ys -> (+#) `appFL` (lengthFL `appFL` ys) `appFL` P.return (IntFL 1)
  nullFL = returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.return TrueFL
    ConsFL _ _ -> P.return FalseFL
  maximumFL = foldl1FL `appFL` maxFL
  minimumFL = foldl1FL `appFL` minFL
  -- TODO: originally strict
  sumFL = foldlFL `appFL` (+#) `appFL` (fromIntegerFL `appFL` P.return (IntegerFL 0))
  -- TODO: originally strict
  productFL = foldlFL `appFL` (*#) `appFL` (fromIntegerFL `appFL` P.return (IntegerFL 1))
  toListFL = idFL
  --TODO: add missing implementations
  {-elem    = List.elem
  foldl   = List.foldl
  foldl'  = List.foldl'
  foldl1  = List.foldl1
  foldr   = List.foldr
  foldr1  = List.foldr1
  length  = List.length
  maximum = List.maximum
  minimum = List.minimum
  null    = List.null
  product = List.product
  sum     = List.sum
  toList  = id-}

allFL :: forall t a. FoldableFL t
      => FL ((a :--> BoolFL FL) :--> t a :--> BoolFL FL)
allFL = returnFLF $ \p' -> share p' P.>>= \p -> foldrFL `appFL` returnFLF (\x -> returnFLF $ \acc -> (&&#) `appFL` (p `appFL` x) `appFL` acc) `appFL` P.return TrueFL

anyFL :: forall t a. FoldableFL t
      => FL ((a :--> BoolFL FL) :--> t a :--> BoolFL FL)
anyFL = returnFLF $ \p' -> share p' P.>>= \p -> foldrFL `appFL` returnFLF (\x -> returnFLF $ \acc -> (||#) `appFL` (p `appFL` x) `appFL` acc) `appFL` P.return FalseFL

andFL :: forall t. FoldableFL t
      => FL (t (BoolFL FL) :--> BoolFL FL)
andFL = foldrFL `appFL` (&&#) `appFL` P.return TrueFL

orFL :: forall t. FoldableFL t
     => FL (t (BoolFL FL) :--> BoolFL FL)
orFL = foldrFL `appFL` (||#) `appFL` P.return TrueFL

data BoolFL (m :: Type -> Type) = FalseFL | TrueFL

boolFLtoBool :: BoolFL FL -> Bool
boolFLtoBool FalseFL = False
boolFLtoBool TrueFL  = True

type instance Lifted m Bool = BoolFL m

instance HasPrimitiveInfo (BoolFL FL) where
  primitiveInfo = NoPrimitive

instance Instantiatable (BoolFL FL) where
  instantiate = [P.return FalseFL, P.return TrueFL]

instance To Bool where
  toWith _ False = FalseFL
  toWith _ True = TrueFL

instance From Bool where
  from FalseFL = False
  from TrueFL  = True

instance Unifiable Bool where
  unify = lazyUnify
  lazyUnify FalseFL FalseFL = P.return ()
  lazyUnify TrueFL  TrueFL  = P.return ()
  lazyUnify _       _       = P.empty

instance NormalForm Bool where
  normalFormWith _ FalseFL = P.return FalseFL
  normalFormWith _ TrueFL  = P.return TrueFL

instance ShowFree Bool where
  showFree' False = "False"
  showFree' True  = "True"

instance Invertible Bool

data UnitFL (m :: Type -> Type) = UnitFL

type instance Lifted m () = UnitFL m

instance HasPrimitiveInfo (UnitFL FL) where
  primitiveInfo = NoPrimitive

instance Instantiatable (UnitFL FL) where
  instantiate = [P.return UnitFL]

instance To () where
  toWith _ () = UnitFL

instance From () where
  from UnitFL = ()

instance Unifiable () where
  unify = lazyUnify
  lazyUnify UnitFL UnitFL = P.return ()

instance NormalForm () where
  normalFormWith _ UnitFL = P.return UnitFL

instance ShowFree () where
  showFree' () = "()"

instance Invertible ()

data OrderingFL (m :: Type -> Type) = LTFL | EQFL | GTFL

type instance Lifted m Ordering = OrderingFL m

instance HasPrimitiveInfo (OrderingFL FL) where
  primitiveInfo = NoPrimitive

instance Instantiatable (OrderingFL FL) where
  instantiate = [P.return LTFL, P.return EQFL, P.return GTFL]

instance To Ordering where
  toWith _ LT = LTFL
  toWith _ EQ = EQFL
  toWith _ GT = GTFL

instance From Ordering where
  from = \case
    LTFL -> LT
    EQFL -> EQ
    GTFL -> GT

instance Unifiable Ordering where
  unify = lazyUnify
  lazyUnify LTFL LTFL = P.return ()
  lazyUnify EQFL EQFL = P.return ()
  lazyUnify GTFL GTFL = P.return ()
  lazyUnify _    _    = P.empty

instance NormalForm Ordering where
  normalFormWith _ LTFL = P.return LTFL
  normalFormWith _ EQFL = P.return EQFL
  normalFormWith _ GTFL = P.return GTFL

instance ShowFree Ordering where
  showFree' LT = "LT"
  showFree' EQ = "EQ"
  showFree' GT = "GT"

instance Invertible Ordering

instance HasPrimitiveInfo (IntegerFL FL) where
  primitiveInfo = Primitive

instance To Integer where
  toWith _ = IntegerFL

instance From Integer where
  from (IntegerFL x) = x

instance Unifiable Integer where
  unify = lazyUnify
  lazyUnify (IntegerFL x) (IntegerFL y) = P.guard (x P.== y)

instance NormalForm Integer where
  normalFormWith _ (IntegerFL x) = P.return (IntegerFL x)

instance ShowFree Integer where
  showFree' = P.show

instance Invertible Integer

instance HasPrimitiveInfo (IntFL FL) where
  primitiveInfo = Primitive

instance To Int where
  toWith _ = P.coerce

instance From Int where
  from = P.coerce

instance Unifiable Int where
  unify = lazyUnify
  lazyUnify (IntFL x) (IntFL y) = P.guard (x P.== y)

instance NormalForm Int where
  normalFormWith _ (IntFL x) = P.return (IntFL x)

instance ShowFree Int where
  showFree' = P.show

instance Invertible Int

instance HasPrimitiveInfo (FloatFL FL) where
  primitiveInfo = Primitive

instance To Float where
  toWith _ = P.coerce

instance From Float where
  from = P.coerce

instance Unifiable Float where
  unify = lazyUnify
  lazyUnify (FloatFL x) (FloatFL y) = P.guard (x P.== y)

instance NormalForm Float where
  normalFormWith _ (FloatFL x) = P.return (FloatFL x)

instance ShowFree Float where
  showFree' = P.show

instance Invertible Float

instance HasPrimitiveInfo (DoubleFL FL) where
  primitiveInfo = Primitive

instance To Double where
  toWith _ = P.coerce

instance From Double where
  from = P.coerce

instance Unifiable Double where
  unify = lazyUnify
  lazyUnify (DoubleFL x) (DoubleFL y) = P.guard (x P.== y)

instance NormalForm Double where
  normalFormWith _ (DoubleFL x) = P.return (DoubleFL x)

instance ShowFree Double where
  showFree' = P.show

instance Invertible Double

instance HasPrimitiveInfo (CharFL FL) where
  primitiveInfo = Primitive

instance To P.Char where
  toWith _ = P.coerce

instance From P.Char where
  from = P.coerce

instance Unifiable P.Char where
  unify = lazyUnify
  lazyUnify (CharFL x) (CharFL y) = P.guard (x P.== y)

instance NormalForm P.Char where
  normalFormWith _ (CharFL x) = P.return (CharFL x)

instance ShowFree P.Char where
  showFree' = P.show

instance Invertible P.Char

-- | Lifted ShowS type
type ShowSFL m = (-->) m (StringFL m) (StringFL m)

type instance Lifted FL P.Show = ShowFL
type instance Lifted FL (P.Show f) = ShowFL (Lifted FL f)
-- | Lifted Show type class
class ShowFL a where
  {-# MINIMAL showsPrecFL | showFL #-}
  showsPrecFL :: FL (IntFL FL :--> a :--> ShowSFL FL)
  showsPrecFL = returnFLF $ \_ -> returnFLF $ \x -> returnFLF $ \s ->
    apply2FL (++#) (showFL `appFL` x) s

  showFL :: FL (a :--> StringFL FL)
  showFL = returnFLF $ \x -> apply2FL showsFLNoShare x (P.return NilFL)

  showListFL :: FL (ListFL FL a :--> ShowSFL FL)
  showListFL = returnFLF $ \ls -> returnFLF $ \s -> apply3FL showsList__ showsFLNoShare ls s

showsList__ :: FL ((a :--> ShowSFL FL) :--> ListFL FL a :--> ShowSFL FL)
showsList__ = returnFLF $ \showx' -> share showx' P.>>= \showx -> returnFLF $ \list -> returnFLF $ \s ->
  list P.>>= \case
    NilFL       -> apply2FL (++#) (toFL "[]") s
    ConsFL x xs ->
      P.return (ConsFL (toFL '[') (apply2FL showx x (apply3FL showl showx xs s)))
  where
    showl = returnFLF $ \showx -> returnFLF $ \list -> returnFLF $ \s ->
      list P.>>= \case
        NilFL       ->
          P.return (ConsFL (toFL ']') s)
        ConsFL y ys ->
          P.return (ConsFL (toFL ',')
            (apply2FL showx y (apply3FL showl showx ys s)))

shows :: P.Show a => a -> P.ShowS
shows = P.showsPrec 0

showsFL :: ShowFL a => FL (a :--> ShowSFL FL)
showsFL = showsPrecFL `appFL` toFL 0

showsFLNoShare :: ShowFL a => FL (a :--> ShowSFL FL)
showsFLNoShare = showsPrecFL `appFL` toFL 0

showString :: P.String -> P.ShowS
showString = (P.++)

showStringFL :: FL (StringFL FL :--> ShowSFL FL)
showStringFL = (++#)

showCommaSpace :: P.ShowS
showCommaSpace = showString ", "

showCommaSpaceFL :: FL (ShowSFL FL)
showCommaSpaceFL = showStringFL `appFL` toFL ", "

showSpace :: P.ShowS
showSpace =  showString " "

showSpaceFL :: FL (ShowSFL FL)
showSpaceFL =  showStringFL `appFL` toFL " "

showParen :: Bool -> P.ShowS -> P.ShowS
showParen b s = if b then showString "(" P.. (s P.. showString ")") else s

showParenFL :: FL (BoolFL FL :--> ShowSFL FL :--> ShowSFL FL)
showParenFL = returnFLF $ \b -> returnFLF $ \s -> b P.>>= \case
  TrueFL  -> apply2FL (.#) (showStringFL `appFL` toFL "(")
          (apply2FL (.#) s (showStringFL `appFL` toFL ")"))
  FalseFL -> s

instance ShowFL (BoolFL FL) where
  showFL = liftFL1Convert P.show

instance ShowFL (UnitFL FL) where
  showFL = liftFL1Convert P.show

instance ShowFL (IntFL FL) where
  showFL = liftFL1Convert P.show

instance ShowFL (IntegerFL FL) where
  showFL = liftFL1Convert P.show

instance ShowFL (FloatFL FL) where
  showFL = liftFL1Convert P.show

instance ShowFL (DoubleFL FL) where
  showFL = liftFL1Convert P.show

instance ShowFL (CharFL FL) where
  showFL = liftFL1Convert P.show
  showListFL = returnFLF $ \x -> groundNormalFormFL x P.>>= \v -> toFL (P.showList (from v))

instance ShowFL a => ShowFL (ListFL FL a) where
  showFL = returnFLF $ \xs -> apply2FL showListFL xs (P.return NilFL)


-- * Lifted Eq type class, instances and functions

type instance Lifted FL P.Eq = EqFL
type instance Lifted FL (P.Eq f) = EqFL (Lifted FL f)
-- | Lifted Eq type class
class EqFL a where
  (==#) :: FL (a :--> a :--> BoolFL FL)
  (==#) = returnFLF $ \a1 -> returnFLF $ \a2 -> notFL `appFL` apply2FL (/=#) a1 a2

  (/=#) :: FL (a :--> a :--> BoolFL FL)
  (/=#) = returnFLF $ \a1 -> returnFLF $ \a2 -> notFL `appFL` apply2FL (==#) a1 a2

instance EqFL (BoolFL FL) where
  (==#) = liftFL2Convert (P.==)
  (/=#) = liftFL2Convert (P./=)

instance EqFL (OrderingFL FL) where
  (==#) = liftFL2Convert (P.==)
  (/=#) = liftFL2Convert (P./=)

instance EqFL (UnitFL FL) where
  (==#) = liftFL2Convert (P.==)
  (/=#) = liftFL2Convert (P./=)

instance EqFL (IntFL FL) where
  (==#) = primitiveOrd2 (P.==) (P.Just eqConstraint)
  (/=#) = primitiveOrd2 (P./=) (P.Just neqConstraint)

instance EqFL (IntegerFL FL) where
  (==#) = primitiveOrd2 (P.==) (P.Just eqConstraint)
  (/=#) = primitiveOrd2 (P./=) (P.Just neqConstraint)

instance EqFL (FloatFL FL) where
  (==#) = primitiveOrd2 (P.==) (P.Just eqConstraint)
  (/=#) = primitiveOrd2 (P./=) (P.Just neqConstraint)

instance EqFL (DoubleFL FL) where
  (==#) = primitiveOrd2 (P.==) (P.Just eqConstraint)
  (/=#) = primitiveOrd2 (P./=) (P.Just neqConstraint)

instance EqFL (CharFL FL) where
  (==#) = primitiveOrd2 (P.==) (P.Just eqConstraint)
  (/=#) = primitiveOrd2 (P./=) (P.Just neqConstraint)

instance EqFL a => EqFL (ListFL FL a) where
  (==#) = returnFLF $ \a1 -> returnFLF $ \a2 -> a1 P.>>= \case
    NilFL       -> a2 P.>>= \case
      NilFL       -> P.return TrueFL
      ConsFL _ _  -> P.return FalseFL
    ConsFL x xs -> a2 P.>>= \case
      NilFL       -> P.return FalseFL
      ConsFL y ys -> eqOn2 x y xs ys

instance EqFL a => EqFL (RatioFL FL a) where
  (==#) = returnFLF $ \x1 -> returnFLF $ \x2 -> do
    (a1 :%# b1) <- x1
    (a2 :%# b2) <- x2
    eqOn2 a1 a2 b1 b2

eqOn2 :: (EqFL a1, EqFL a2)
      => FL a1 -> FL a1 -> FL a2 -> FL a2 -> FL (BoolFL FL)
eqOn2 x y xs ys = apply2FL (&&#) (apply2FL (==#) x y) (apply2FL (==#) xs ys)

-- * Lifted Ord type class, instances and functions

type instance Lifted FL P.Ord = OrdFL
type instance Lifted FL (P.Ord f) = OrdFL (Lifted FL f)
-- | Lifted Ord type class
class EqFL a => OrdFL a where
  {-# MINIMAL compareFL | (<=#) #-}
  compareFL :: FL (a :--> a :--> OrderingFL FL)
  compareFL = returnFLF $ \a1' -> share a1' P.>>= \a1 -> returnFLF $ \a2' -> share a2' P.>>= \a2 ->
    apply2FL (==#) a1 a2 P.>>= \case
      TrueFL  -> P.return EQFL
      FalseFL -> apply2FL (<=#) a1 a2 P.>>= \case
        TrueFL  -> P.return LTFL
        FalseFL -> P.return GTFL

  (<#) :: FL (a :--> a :--> BoolFL FL)
  (<#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compareFL a1 a2 P.>>= \case
      LTFL -> P.return TrueFL
      _    -> P.return FalseFL

  (<=#) :: FL (a :--> a :--> BoolFL FL)
  (<=#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compareFL a1 a2 P.>>= \case
      GTFL -> P.return FalseFL
      _    -> P.return TrueFL

  (>#) :: FL (a :--> a :--> BoolFL FL)
  (>#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compareFL a1 a2 P.>>= \case
      GTFL -> P.return TrueFL
      _    -> P.return FalseFL

  (>=#) :: FL (a :--> a :--> BoolFL FL)
  (>=#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compareFL a1 a2 P.>>= \case
      LTFL -> P.return FalseFL
      _    -> P.return TrueFL

  maxFL :: FL (a :--> a :--> a)
  maxFL = returnFLF $ \a1' -> share a1' P.>>= \a1 -> returnFLF $ \a2' -> share a2' P.>>= \a2 ->
    apply2FL (>=#) a1 a2 P.>>= \case
      TrueFL -> a1
      _      -> a2

  minFL :: FL (a :--> a :--> a)
  minFL = returnFLF $ \a1' -> share a1' P.>>= \a1 -> returnFLF $ \a2' -> share a2' P.>>= \a2 ->
    apply2FL (<=#) a1 a2 P.>>= \case
      TrueFL -> a1
      _      -> a2

instance OrdFL (BoolFL FL) where
  compareFL = liftFL2Convert P.compare

instance OrdFL (UnitFL FL) where
  compareFL = liftFL2Convert P.compare

instance OrdFL (IntFL FL) where
  (>=#) = primitiveOrd2 (P.>=) intGeqConstraint
  (<=#) = primitiveOrd2 (P.<=) intLeqConstraint
  (>#)  = primitiveOrd2 (P.>)  intGtConstraint
  (<#)  = primitiveOrd2 (P.<)  intLtConstraint
  maxFL = primitive2    P.max  intMaxConstraint
  minFL = primitive2    P.max  intMinConstraint

instance OrdFL (IntegerFL FL) where
  (>=#) = primitiveOrd2 (P.>=) integerGeqConstraint
  (<=#) = primitiveOrd2 (P.<=) integerLeqConstraint
  (>#)  = primitiveOrd2 (P.>)  integerGtConstraint
  (<#)  = primitiveOrd2 (P.<)  integerLtConstraint
  maxFL = primitive2    P.max  integerMaxConstraint
  minFL = primitive2    P.min  integerMinConstraint

instance OrdFL (FloatFL FL) where
  (>=#) = primitiveOrd2 (P.>=) floatGeqConstraint
  (<=#) = primitiveOrd2 (P.<=) floatLeqConstraint
  (>#)  = primitiveOrd2 (P.>)  floatGtConstraint
  (<#)  = primitiveOrd2 (P.<)  floatLtConstraint
  maxFL = primitive2    P.max  floatMaxConstraint
  minFL = primitive2    P.min  floatMinConstraint

instance OrdFL (DoubleFL FL) where
  (>=#) = primitiveOrd2 (P.>=) doubleGeqConstraint
  (<=#) = primitiveOrd2 (P.<=) doubleLeqConstraint
  (>#)  = primitiveOrd2 (P.>)  doubleGtConstraint
  (<#)  = primitiveOrd2 (P.<)  doubleLtConstraint
  maxFL = primitive2    P.max  doubleMaxConstraint
  minFL = primitive2    P.min  doubleMinConstraint

instance OrdFL (CharFL FL) where
  (>=#) = primitiveOrd2 (P.>=) charGeqConstraint
  (<=#) = primitiveOrd2 (P.<=) charLeqConstraint
  (>#)  = primitiveOrd2 (P.>)  charGtConstraint
  (<#)  = primitiveOrd2 (P.<)  charLtConstraint
  maxFL = primitive2    P.max  charMaxConstraint
  minFL = primitive2    P.min  charMinConstraint

instance OrdFL a => OrdFL (ListFL FL a) where
  compareFL = returnFLF $ \x -> returnFLF $ \y ->
    x P.>>= \x' -> y P.>>= \y' -> case (x', y') of
      (NilFL      , NilFL      ) -> P.return EQFL
      (NilFL      , ConsFL _ _ ) -> P.return LTFL
      (ConsFL _ _ , NilFL      ) -> P.return GTFL
      (ConsFL a as, ConsFL b bs) -> apply2FL compareFL a b P.>>= \case
        EQFL -> apply2FL compareFL as bs
        o  -> P.return o

-- * Lifted Num type class, instances and functions

type instance Lifted FL P.Num = NumFL
type instance Lifted FL (P.Num f) = NumFL (Lifted FL f)
-- | Lifted Num type class
class NumFL a where
  (+#) :: FL (a :--> a :--> a)
  (-#) :: FL (a :--> a :--> a)
  (-#) = returnFLF $ \a -> returnFLF $ \b ->
    (+#) `appFL` a `appFL` (negateFL `appFL` b)
  (*#) :: FL (a :--> a :--> a)
  negateFL :: FL (a :--> a)
  negateFL = returnFLF $ \a -> (-#) `appFL` (fromIntegerFL `appFL` toFL 0) `appFL` a
  absFL    :: FL (a :--> a)
  signumFL :: FL (a :--> a)
  fromIntegerFL :: FL (IntegerFL FL :--> a)

instance NumFL (IntFL FL) where
  (+#) = primitive2 (P.+) intPlusConstraint
  (-#) = primitive2 (P.-) intMinusConstraint
  (*#) = primitive2 (P.*) intMulConstraint
  negateFL = primitive1 P.negate intNegateConstraint
  absFL    = primitive1 P.abs    intAbsConstraint
  signumFL = primitive1 P.signum intSignumConstraint
  fromIntegerFL = liftFL1Convert P.fromInteger --TODO:

instance NumFL (IntegerFL FL) where
  (+#) = primitive2 (P.+) integerPlusConstraint
  (-#) = primitive2 (P.-) integerMinusConstraint
  (*#) = primitive2 (P.*) integerMulConstraint
  negateFL = primitive1 P.negate integerNegateConstraint
  absFL    = primitive1 P.abs    integerAbsConstraint
  signumFL = primitive1 P.signum integerSignumConstraint
  fromIntegerFL = returnFLF P.id

instance NumFL (FloatFL FL) where
  (+#) = primitive2 (P.+) floatPlusConstraint
  (-#) = primitive2 (P.-) floatMinusConstraint
  (*#) = primitive2 (P.*) floatMulConstraint
  negateFL = primitive1 P.negate floatNegateConstraint
  absFL    = primitive1 P.abs    floatAbsConstraint
  signumFL = primitive1 P.signum floatSignumConstraint
  fromIntegerFL = liftFL1Convert P.fromInteger

instance NumFL (DoubleFL FL) where
  (+#) = primitive2 (P.+) doublePlusConstraint
  (-#) = primitive2 (P.-) doubleMinusConstraint
  (*#) = primitive2 (P.*) doubleMulConstraint
  negateFL = primitive1 P.negate doubleNegateConstraint
  absFL    = primitive1 P.abs    doubleAbsConstraint
  signumFL = primitive1 P.signum doubleSignumConstraint
  fromIntegerFL = liftFL1Convert P.fromInteger
-- * Lifted Fractional type class, instances and functions

type instance Lifted FL P.Fractional = FractionalFL
type instance Lifted FL (P.Fractional f) = FractionalFL (Lifted FL f)
-- | Lifted Fractional type class
class NumFL a => FractionalFL a where
  {-# MINIMAL fromRationalFL, (recipFL | (/#)) #-}

  (/#) :: FL (a :--> a :--> a)
  (/#) = returnFLF $ \x -> returnFLF $ \y -> apply2FL (*#) x  (recipFL `appFL` y)

  recipFL :: FL (a :--> a)
  recipFL = returnFLF $ \x -> apply2FL (/#) (fromIntegerFL `appFL` toFL 1) x

  fromRationalFL :: FL (RationalFL FL :--> a)

instance FractionalFL (FloatFL FL) where
  (/#) = primitive2 (P./) floatDivConstraint
  fromRationalFL = liftFL1Convert P.fromRational

instance FractionalFL (DoubleFL FL) where
  (/#) = primitive2 (P./) doubleDivConstraint
  fromRationalFL = liftFL1Convert P.fromRational

-- * Lifted Real type class, instances and functions

type instance Lifted FL P.Real = RealFL
type instance Lifted FL (P.Real f) = RealFL (Lifted FL f)
-- | Lifted Real type class
class (NumFL a, OrdFL a) => RealFL a where
  toRationalFL :: FL (a :--> RationalFL FL)

instance RealFL (IntFL FL) where
  toRationalFL = liftFL1Convert P.toRational

instance RealFL (IntegerFL FL) where
  toRationalFL = liftFL1Convert P.toRational

instance RealFL (FloatFL FL) where
  toRationalFL = liftFL1Convert P.toRational

instance RealFL (DoubleFL FL) where
  toRationalFL = liftFL1Convert P.toRational

-- * Lifted Integral type class, instances and functions

type instance Lifted FL P.Integral = IntegralFL
type instance Lifted FL (P.Integral f) = IntegralFL (Lifted FL f)
-- | Lifted Integral type class
class (RealFL a, EnumFL a) => IntegralFL a where
  quotFL      :: FL (a :--> a :--> a)
  remFL       :: FL (a :--> a :--> a)
  divFL       :: FL (a :--> a :--> a)
  modFL       :: FL (a :--> a :--> a)
  quotRemFL   :: FL (a :--> a :--> Tuple2FL FL a a)
  divModFL    :: FL (a :--> a :--> Tuple2FL FL a a)
  toIntegerFL :: FL (a :--> IntegerFL FL)

  quotFL   = returnFLF $ \n -> returnFLF $ \d -> fstFL `appFL` apply2FL quotRemFL n d
  remFL    = returnFLF $ \n -> returnFLF $ \d -> sndFL `appFL` apply2FL quotRemFL n d
  divFL    = returnFLF $ \n -> returnFLF $ \d -> fstFL `appFL` apply2FL divModFL n d
  modFL    = returnFLF $ \n -> returnFLF $ \d -> sndFL `appFL` apply2FL divModFL n d

  divModFL = returnFLF $ \n -> returnFLF $ \d' -> share d' P.>>= \d ->
    share (apply2FL quotRemFL n d) P.>>= \qr ->
    qr P.>>= \(Tuple2FL q r') -> share r' P.>>= \r -> apply2FL (==#) (signumFL `appFL` r)
                                                               (negateFL `appFL` (signumFL `appFL` d))
       P.>>= \case
         TrueFL -> P.return (Tuple2FL (apply2FL (-#) q
                                 (fromIntegerFL `appFL` toFL 1))
                                 (apply2FL (+#) r d))
         FalseFL -> qr

instance IntegralFL (IntFL FL) where
  quotFL      = primitive2     P.quot      intQuotConstraint
  remFL       = primitive2     P.rem       intRemConstraint
  divFL       = primitive2     P.div       intDivConstraint
  modFL       = primitive2     P.mod       intModConstraint
  divModFL    = primitive2Pair P.divMod    P.undefined
  quotRemFL   = primitive2Pair P.quotRem   P.undefined
  toIntegerFL = liftFL1Convert P.toInteger --TODO: constraint

instance IntegralFL (IntegerFL FL) where
  quotFL      = primitive2     P.quot    integerQuotConstraint
  remFL       = primitive2     P.rem     integerRemConstraint
  divFL       = primitive2     P.div     integerDivConstraint
  modFL       = primitive2     P.mod     integerModConstraint
  divModFL    = primitive2Pair P.divMod  P.undefined
  quotRemFL   = primitive2Pair P.quotRem P.undefined
  toIntegerFL = returnFLF P.id

-- * Lifted Monad & Co type classes and instances

infixl 1 >>=#, >>#
infixl 4 <$#, <*#, *>#, <*>#

type instance Lifted FL P.Functor = FunctorFL
type instance Lifted FL (P.Functor f) = FunctorFL (Lifted FL f)
-- | Lifted Functor type class
class FunctorFL f where
  fmapFL :: forall a b. FL ((a :--> b) :--> f a :--> f b)
  (<$#) :: forall a b. FL (a :--> f b :--> f a)
  (<$#) = returnFLF $ \a -> returnFLF $ \f ->
    apply2FL fmapFL (constFL `appFL` a) f

instance FunctorFL (ListFL FL) where
  fmapFL = returnFLF $ \f' -> share f' P.>>= \f -> returnFLF $ \l -> l P.>>= \case
    NilFL       -> P.return NilFL
    ConsFL x xs -> P.return (ConsFL (f `appFL` x) (apply2FL fmapFL f xs))

(<$>#) :: forall f a b. FunctorFL f
       => FL ((a :--> b) :--> (f a :--> f b))
(<$>#) = fmapFL

type instance Lifted FL P.Applicative = ApplicativeFL
type instance Lifted FL (P.Applicative f) = ApplicativeFL (Lifted FL f)
-- | Lifted Applicative type class
class FunctorFL f => ApplicativeFL f where
  pureFL :: forall a. FL (a :--> f a)

  (<*>#) :: forall a b. FL (f (a :--> b) :--> f a :--> f b)
  (<*>#) = returnFLF $ \f -> returnFLF $ \a ->
    apply3FL liftA2FL (liftFL1 P.id) f a

  liftA2FL :: forall a b c. FL ((a :--> b :--> c) :--> f a :--> f b :--> f c)
  liftA2FL = returnFLF $ \f -> returnFLF $ \a -> returnFLF $ \b ->
    apply2FL (<*>#) (apply2FL fmapFL f a) b

  (*>#) :: forall a b. FL (f a :--> f b :--> f b)
  (*>#) = returnFLF $ \a -> returnFLF $ \b ->
    apply3FL liftA2FL (liftFL2 (P.const P.id)) a b

  (<*#) :: forall a b. FL (f a :--> f b :--> f a)
  (<*#) = returnFLF $ \a -> returnFLF $ \b ->
    apply3FL liftA2FL constFL a b
  {-# MINIMAL pureFL, ((<*>#) | liftA2FL) #-}

instance ApplicativeFL (ListFL FL) where
  pureFL = returnFLF $ \a -> P.return (ConsFL a (P.return NilFL))
  (<*>#) = returnFLF $ \fs -> returnFLF $ \as ->
    apply2FL concatMapFL (returnFLF $ \a ->
    apply2FL fmapFL      (returnFLF $ \f -> f `appFL` a) fs) as

type instance Lifted FL P.Alternative = AlternativeFL
type instance Lifted FL (P.Alternative f) = AlternativeFL (Lifted FL f)
-- | Lifted Alternative type class
class ApplicativeFL f => AlternativeFL f where
  emptyFL :: forall a. FL (f a)
  (<|>#) :: forall a. FL (f a :--> f a :--> f a)
  someFL  :: forall a. FL (f a :--> f (ListFL FL a))
  someFL = returnFLF $ \v' -> share v' P.>>= \v ->
    let many_v = apply2FL (<|>#) some_v (pureFL `appFL` P.return NilFL)
        some_v = apply3FL liftA2FL consFL v many_v
        consFL = returnFLF $ \x -> returnFLF $ \y -> P.return (ConsFL x y)
    in some_v
  manyFL  :: forall a. FL (f a :--> f (ListFL FL a))
  manyFL = returnFLF $ \v' -> share v' P.>>= \v ->
    let many_v = apply2FL (<|>#) some_v (pureFL `appFL` P.return NilFL)
        some_v = apply3FL liftA2FL consFL v many_v
        consFL = returnFLF $ \x -> returnFLF $ \y -> P.return (ConsFL x y)
    in many_v

instance AlternativeFL (ListFL FL) where
  emptyFL = P.return NilFL
  (<|>#) = (++#)


type instance Lifted FL P.Monad = MonadFL
type instance Lifted FL (P.Monad f) = MonadFL (Lifted FL f)
-- | Lifted Monad type class
class ApplicativeFL m => MonadFL m where
  (>>=#) :: forall a b. FL (m a :--> (a :--> m b) :--> m b)
  (>>#)  :: forall a b. FL (m a :--> m b :--> m b)
  (>>#) = returnFLF $ \a -> returnFLF $ \b ->
    apply2FL (>>=#) a (returnFLF (P.const b))
  returnFL :: forall a. FL (a :--> m a)
  returnFL = pureFL
  {-# MINIMAL (>>=#) #-}

instance MonadFL (ListFL FL) where
  (>>=#) = returnFLF $ \a -> returnFLF $ \f' -> share f' P.>>= \f -> a P.>>= \case
    NilFL       -> P.return NilFL
    ConsFL x xs -> apply2FL (++#) (f `appFL` x) (apply2FL (>>=#) xs f)

type instance Lifted FL P.MonadFail = MonadFailFL
type instance Lifted FL (P.MonadFail f) = MonadFailFL (Lifted FL f)
-- | Lifted MonadFail type class
class MonadFL m => MonadFailFL m where
  failFL :: forall a. FL (StringFL FL :--> m a)

instance MonadFailFL (ListFL FL) where
  failFL = returnFLF $ \_ -> P.return NilFL

-- * Lifted Enum type class, instances and functions

type instance Lifted FL P.Enum = EnumFL
type instance Lifted FL (P.Enum f) = EnumFL (Lifted FL f)
-- | Lifted Enum type class
class EnumFL a where
  succFL :: FL (a :--> a)
  succFL = returnFLF $ \a ->
    toEnumFL `appFL` apply2FL (+#) (toFL 1) (fromEnumFL `appFL` a)
  predFL :: FL (a :--> a)
  predFL = returnFLF $ \a ->
    toEnumFL `appFL` apply2FL (-#) (toFL 1) (fromEnumFL `appFL` a)

  toEnumFL   :: FL (IntFL FL :--> a)
  fromEnumFL :: FL (a :--> IntFL FL)

  enumFromFL       :: FL (a               :--> ListFL FL a)
  enumFromFL       = returnFLF $ \x1 ->
    apply2FL mapFLNoShare toEnumFL (enumFromFL `appFL`
      (fromEnumFL `appFL` x1))

  enumFromThenFL   :: FL (a :--> a        :--> ListFL FL a)
  enumFromThenFL   = returnFLF $ \x1 -> returnFLF $ \x2 ->
    apply2FL mapFLNoShare toEnumFL (apply2FL enumFromThenFL
      (fromEnumFL `appFL` x1) (fromEnumFL `appFL` x2))

  enumFromToFL     :: FL (a        :--> a :--> ListFL FL a)
  enumFromToFL     = returnFLF $ \x1 ->                   returnFLF $ \x3 ->
    apply2FL mapFLNoShare toEnumFL (apply2FL enumFromToFL
      (fromEnumFL `appFL` x1)                         (fromEnumFL `appFL` x3))

  enumFromThenToFL :: FL (a :--> a :--> a :--> ListFL FL a)
  enumFromThenToFL = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    apply2FL mapFLNoShare toEnumFL (apply3FL enumFromThenToFL
      (fromEnumFL `appFL` x1) (fromEnumFL `appFL` x2) (fromEnumFL `appFL` x3))

instance EnumFL (IntFL FL) where
  succFL = (+#) `appFL` toFL 1
  predFL = (-#) `appFL` toFL 1

  toEnumFL   = returnFLF P.id
  fromEnumFL = returnFLF P.id

  enumFromFL = returnFLF $ \x1 ->
    x1 P.>>= \(IntFL v1) ->
    toFL (P.map P.fromIntegral (P.enumFrom v1))

  enumFromThenFL = returnFLF $ \x1 -> returnFLF $ \x2 ->
    x1 P.>>= \(IntFL v1) -> x2 P.>>= \(IntFL v2) ->
    toFL (P.map P.fromIntegral (P.enumFromThen v1 v2))

  enumFromToFL = returnFLF $ \x1 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntFL v1) -> x3 P.>>= \(IntFL v3) ->
    toFL (P.map P.fromIntegral (P.enumFromTo v1 v3))

  enumFromThenToFL = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntFL v1) -> x2 P.>>= \(IntFL v2) -> x3 P.>>= \(IntFL v3) ->
    toFL (P.map P.fromIntegral (P.enumFromThenTo v1 v2 v3))

instance EnumFL (IntegerFL FL) where
  succFL = (+#) `appFL` toFL 1
  predFL = (-#) `appFL` toFL 1

  toEnumFL   = toIntegerFL
  fromEnumFL = fromIntegerFL

  enumFromFL = returnFLF $ \x1 ->
    x1 P.>>= \(IntegerFL v1) ->
    toFL (P.enumFrom v1)

  enumFromThenFL = returnFLF $ \x1 -> returnFLF $ \x2 ->
    x1 P.>>= \(IntegerFL v1) -> x2 P.>>= \(IntegerFL v2) ->
    toFL (P.enumFromThen v1 v2)

  enumFromToFL = returnFLF $ \x1 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntegerFL v1) -> x3 P.>>= \(IntegerFL v3) ->
    toFL (P.enumFromTo v1 v3)

  enumFromThenToFL = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntegerFL v1) -> x2 P.>>= \(IntegerFL v2) -> x3 P.>>= \(IntegerFL v3) ->
    toFL (P.enumFromThenTo v1 v2 v3)

-- * Lifted Bounded type class, instances and functions

type instance Lifted FL P.Bounded = BoundedFL
type instance Lifted FL (P.Bounded f) = BoundedFL (Lifted FL f)
-- | Lifted Bounded type class
class BoundedFL a where
  minBoundFL :: FL a
  maxBoundFL :: FL a

instance BoundedFL (IntFL FL) where
  minBoundFL = toFL P.minBound
  maxBoundFL = toFL P.maxBound

type instance Lifted FL P.IsString = IsStringFL
type instance Lifted FL (P.IsString f) = IsStringFL (Lifted FL f)
class IsStringFL a where
  fromStringFL :: FL (StringFL FL :--> a)

instance (a ~ CharFL FL) => IsStringFL (ListFL FL a) where
  fromStringFL = returnFLF P.id

primitive1 :: HasPrimitiveInfo (Lifted FL b) => (a -> b) -> P.Maybe (FLVal (Lifted FL a) -> FLVal (Lifted FL b) -> Constraint) -> FL (Lifted FL a :--> Lifted FL b)
primitive1 f mConstraint = returnFLF $ \x ->
  case mConstraint of
    P.Just constraint -> FL $
      dereference (unFL x) P.>>= \case
        Val a -> unFL $ P.return (coerce (f (coerce a)))
        HaskellVal a -> unFL $ P.return (coerce (f (unsafeCoerce a)))
        x'    -> do
          j <- freshVarID
          assertConstraintND (constraint x' (Var j)) (j: varOf x')
          -- Consistency not necessary, see comment in primitive2
          P.return (Var j)
            where
              varOf (Var i) = [i]
              varOf _       = [] --TODO: auslagern und wiederverwenden
    P.Nothing         -> x P.>>= \a -> P.return (coerce (f (coerce a))) --TODO: unFL überall im Nothing-Branch

--TODO: aufräumen
primitive2 :: HasPrimitiveInfo (Lifted FL c) => (a -> b -> c) -> P.Maybe (FLVal (Lifted FL a) -> FLVal (Lifted FL b) -> FLVal (Lifted FL c) -> Constraint) -> FL (Lifted FL a :--> Lifted FL b :--> Lifted FL c)
primitive2 op mConstraint = returnFLF $ \x -> returnFLF $ \y ->
  case mConstraint of
    P.Just constraint -> FL $
      dereference (unFL x) P.>>= \x' -> dereference (unFL y) P.>>= \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ P.return $ coerce (coerce a `op` coerce b)
          (# Val a, HaskellVal b #) -> unFL $ P.return $ coerce (coerce a `op` unsafeCoerce b)
          (# HaskellVal a, Val b #) -> unFL $ P.return $ coerce (unsafeCoerce a `op` coerce b)
          (# HaskellVal a, HaskellVal b #) -> unFL $ P.return $ coerce (unsafeCoerce a `op` unsafeCoerce b)
          --TODO:
          _                  -> do
            j <- freshVarID
            assertConstraintND (constraint x' y' (Var j)) (j : varsOf x' y')
            -- Diss: Checking consistency is unnecessary, because "j" is fresh.
            -- However, it is important to enter x and y in the set of constrained vars, because
            -- they might get constrained indirectly via "j". Example:
            -- j <- x + y
            -- j <- 1
            -- matchFL 9 x
            -- matchFL 0 y
            P.return (Var j)
            where
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = [] --TODO: auslagern und wiederverwenden
    P.Nothing         -> x P.>>= \a -> y P.>>= \b -> P.return $ coerce (coerce a `op` coerce b)

--TODO: Note on usage, true and false branch are important
--TODO: Important to mention in the disseration, as the implementation differs from the other constraints!
--TODO: why are here no convertible, to or from constraints?
primitiveOrd2 :: (a -> a -> Bool) -> P.Maybe (FLVal (Lifted FL a) -> FLVal (Lifted FL a) -> Constraint) -> FL (Lifted FL a :--> Lifted FL a :--> Lifted FL Bool)
primitiveOrd2 op mConstraint = returnFLF $ \x -> returnFLF $ \y ->
  case mConstraint of
    P.Just constraint -> FL $
      dereference (unFL x) P.>>= \x' -> dereference (unFL y) P.>>= \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ toFL $ coerce a `op` coerce b
          (# Val a, HaskellVal b #) -> unFL $ toFL $ coerce a `op` unsafeCoerce b
          (# HaskellVal a, Val b #) -> unFL $ toFL $ unsafeCoerce a `op` coerce b
          (# HaskellVal a, HaskellVal b #) -> unFL $ toFL $ unsafeCoerce a `op` unsafeCoerce b
          _                  -> trueBranch P.<|> falseBranch
            where
              trueBranch = do
                assertConstraintND (constraint x' y') (varsOf x' y')
                checkConsistencyND -- DISS: optional, iff x and y were unconstrained
                P.return (Val TrueFL)
              falseBranch = do
                assertConstraintND (notConstraint (constraint x' y')) (varsOf x' y')
                checkConsistencyND -- DISS: optional, iff x and y were unconstrained
                P.return (Val FalseFL)
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = []
    P.Nothing         -> x P.>>= \a -> y P.>>= \b -> P.return $ coerce (coerce a `op` coerce b) --TODO: lift2FL-irgendetwas verwenden

--TODO: Use coerce instead of convertible
primitive2Pair :: (From a, From b, To c, To d, HasPrimitiveInfo (Lifted FL c), HasPrimitiveInfo  (Lifted FL d)) => (a -> b -> (c, d)) -> P.Maybe (FLVal (Lifted FL a) -> FLVal (Lifted FL b) -> FLVal (Lifted FL c) -> FLVal (Lifted FL d) -> Constraint) -> FL (Lifted FL a :--> Lifted FL b :--> Lifted FL (c, d))
primitive2Pair op mConstraint = returnFLF $ \x -> returnFLF $ \y ->
  case mConstraint of
    P.Just constraint -> FL $
      dereference (unFL x) P.>>= \x' -> dereference (unFL y) P.>>= \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ toFL $ coerce a `op` coerce b
          (# Val a, HaskellVal b #) -> unFL $ toFL $ coerce a `op` unsafeCoerce b
          (# HaskellVal a, Val b #) -> unFL $ toFL $ unsafeCoerce a `op` coerce b
          (# HaskellVal a, HaskellVal b #) -> unFL $ toFL $ unsafeCoerce a `op` unsafeCoerce b
          _                  -> do
            j <- freshVarID
            k <- freshVarID
            assertConstraintND (constraint x' y' (Var j) (Var k)) (j : k : varsOf x' y')
            -- Diss: Checking consistency is unnecessary, because "j" and "k" are fresh.
            -- However, it is important to enter x and y in the set of constrained vars, because
            -- they might get constrained indirectly via "j". Example:
            -- j <- x + y
            -- j <- 1
            -- matchFL 9 x
            -- matchFL 0 y
            P.return (Val (Tuple2FL (FL $ P.return $ Var j) (FL $ P.return $ Var k)))
            where
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = []
    P.Nothing         -> apply2FL (liftFL2Convert op) x y
