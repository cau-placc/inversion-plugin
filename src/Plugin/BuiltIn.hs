{-# LANGUAGE BangPatterns             #-}
{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleContexts         #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE LambdaCase               #-}
{-# LANGUAGE MagicHash                #-}
{-# LANGUAGE NoStarIsType             #-}
{-# LANGUAGE PolyKinds                #-}
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
import           GHC.Types (RuntimeRep, Type)
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

-- * Lifted tuple types and internal instances

data SoloFL (m :: Type -> Type) a = SoloFL (m a)

type instance Lifted m Solo = SoloFL m
type instance Lifted m (Solo a) = SoloFL m (Lifted m a)

instance HasPrimitiveInfo a => HasPrimitiveInfo (SoloFL FL a) where
  primitiveInfo = NoPrimitive

instance HasPrimitiveInfo a => Narrowable (SoloFL FL a) where
  narrow j = [(SoloFL (free j), 1)]

instance Convertible a => Convertible (Solo a) where
  to (Solo x) = SoloFL (toFL x)
  fromWith ff (SoloFL x) = Solo (ff x)

instance (Convertible a, Matchable a) => Matchable (Solo a) where
  match (Solo x) (SoloFL y) = matchFL x y

instance Unifiable a => Unifiable (Solo a) where
  lazyUnify (SoloFL x) (SoloFL y) = lazyUnifyFL x y

instance NormalForm a => NormalForm (Solo a) where
  normalFormWith nf = \case
    SoloFL x ->
      nf x P.>>= \y ->
        P.return (P.pure (SoloFL y))

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

instance (HasPrimitiveInfo a, HasPrimitiveInfo b) => Narrowable (Tuple2FL FL a b) where
  narrow j = [(Tuple2FL (free j) (free (j P.+ 1)), 2)]

instance (Convertible a, Convertible b) => Convertible (a, b) where
  to (x1, x2) = Tuple2FL (toFL x1) (toFL x2)
  fromWith ff (Tuple2FL x1 x2) = (ff x1, ff x2)

instance (Convertible a, Convertible b, Matchable a, Matchable b) => Matchable (a, b) where
  match (x1, x2) (Tuple2FL y1 y2) = matchFL x1 y1 P.>> matchFL x2 y2

instance (Unifiable a, Unifiable b) => Unifiable (a, b) where
  lazyUnify (Tuple2FL x1 x2) (Tuple2FL y1 y2) = lazyUnifyFL x1 y1 P.>> lazyUnifyFL x2 y2

instance (NormalForm a, NormalForm b) => NormalForm (a, b) where
  normalFormWith nf = \case
    Tuple2FL x1 x2 ->
      nf x1 P.>>= \y1 ->
        nf x2 P.>>= \y2 ->
        P.return (P.pure (Tuple2FL y1 y2))

instance (ShowFree a, ShowFree b) => ShowFree (a, b) where
  showsFreePrec' _ (x1, x2) = P.showString "(" P.. showsFree x1 P.. P.showString "," P.. showsFree x2 P.. P.showString ")"

instance (Invertible a, Invertible b) => Invertible (a, b)

P.concat P.<$> P.mapM genLiftedTupleDataDeclAndInstances [3 .. maxTupleArity]

-- * Lifted list type and internal instances

data ListFL (m :: Type -> Type) a = NilFL | ConsFL (m a) (m (ListFL m a))

type StringFL m = ListFL m (CharFL m)

type instance Lifted m [] = ListFL m
type instance Lifted m [a] = ListFL m (Lifted m a)

instance (HasPrimitiveInfo a, HasPrimitiveInfo (ListFL FL a)) => HasPrimitiveInfo (ListFL FL a) where
  primitiveInfo = NoPrimitive

instance (HasPrimitiveInfo a, HasPrimitiveInfo (ListFL FL a)) => Narrowable (ListFL FL a) where
  narrow j = [(NilFL, 0), (ConsFL (free j) (free (j P.+ 1)), 2)]

instance (Convertible a, Convertible [a]) => Convertible [a] where
  to [] = NilFL
  to (x : xs) = ConsFL (toFL x) (toFL xs)
  fromWith _ NilFL = []
  fromWith ff (ConsFL x xs) = ff x : ff xs

instance (Convertible a, Matchable a, Matchable [a], Convertible [a]) => Matchable [a] where
  match [] NilFL = P.return ()
  match (x : xs) (ConsFL y ys) = matchFL x y P.>> matchFL xs ys
  match _ _ = P.empty

instance (Unifiable a, Unifiable [a]) => Unifiable [a] where
  lazyUnify NilFL NilFL = P.return ()
  lazyUnify (ConsFL x xs) (ConsFL y ys) = lazyUnifyFL x y P.>> lazyUnifyFL xs ys
  lazyUnify _ _ = P.empty

instance (NormalForm a, NormalForm [a]) => NormalForm [a] where
  normalFormWith nf = \case
      NilFL -> P.return (P.pure NilFL)
      ConsFL x xs ->
        nf x P.>>= \y ->
          nf xs P.>>= \ys ->
            P.return (P.pure (ConsFL y ys))

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

instance HasPrimitiveInfo a => Narrowable (MaybeFL FL a) where
  narrow j = [(NothingFL, 0), (JustFL (free j), 1)]

instance Convertible a => Convertible (P.Maybe a) where
  to P.Nothing = NothingFL
  to (P.Just x) = JustFL (toFL x)
  fromWith _ NothingFL = P.Nothing
  fromWith ff (JustFL x) = P.Just (ff x)

instance (Convertible a, Matchable a) => Matchable (P.Maybe a) where
  match P.Nothing NothingFL = P.return ()
  match (P.Just x) (JustFL y) = matchFL x y
  match _ _ = P.empty

instance Unifiable a => Unifiable (P.Maybe a) where
  lazyUnify NothingFL NothingFL = P.return ()
  lazyUnify (JustFL x) (JustFL y) = lazyUnifyFL x y
  lazyUnify _ _ = P.empty

instance NormalForm a => NormalForm (P.Maybe a) where
  normalFormWith nf = \case
      NothingFL -> P.return (P.pure NothingFL)
      JustFL x ->
        nf x P.>>= \y ->
          P.return (P.pure (JustFL y))

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

instance HasPrimitiveInfo a => Narrowable (RatioFL FL a) where
  narrow j = [(free j :%# free (j P.+ 1), 2)]

instance Convertible a => Convertible (P.Ratio a) where
  to (a P.:% b) = toFL a :%# toFL b
  fromWith ff (a :%# b) = ff a P.:% ff b

instance (Convertible a, Matchable a) => Matchable (P.Ratio a) where
  match (a P.:% b) (x :%# y) = matchFL a x P.>> matchFL b y

instance Unifiable a => Unifiable (P.Ratio a) where
  lazyUnify (a :%# b) (x :%# y) = lazyUnifyFL a x P.>> lazyUnifyFL b y

instance NormalForm a => NormalForm (P.Ratio a) where
   normalFormWith nf = \case
       a :%# b ->
         nf a P.>>= \x ->
           nf b P.>>= \y ->
             P.return (P.pure (x :%# y))

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
-- TODO try seq

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
(<##) = liftFL1Convert op
  where
    op (I# i1) (I# i2) = I# (i1 P.<# i2)

(==##) :: FL (IntFL FL :--> IntFL FL :--> IntFL FL)
(==##) = liftFL1Convert op
  where
    op (I# i1) (I# i2) = I# (i1 P.==# i2)

-- * Prelude stuff

fstFL :: FL (Tuple2FL FL a b :--> a)
fstFL = returnFLF $ \x -> x P.>>= \case
  Tuple2FL a _ -> a

sndFL :: FL (Tuple2FL FL a b :--> b)
sndFL = returnFLF $ \x -> x P.>>= \case
  Tuple2FL _ b -> b

undefinedFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . FL a
undefinedFL = P.empty

errorFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . FL (StringFL FL :--> a)
errorFL = failFLStrFL

notFL :: FL (BoolFL FL :--> BoolFL FL)
notFL = liftFL1Convert P.not

idFL :: FL (a :--> a)
idFL = returnFLF P.id

(.#) :: FL ((b :--> c) :--> (a :--> b) :--> a :--> c)
(.#) = returnFLF $ \f -> returnFLF $ \g -> returnFLF $ \a ->
  f `appFL` (g `appFL` a)

flipFL :: FL ((a :--> b :--> c) :--> b :--> a :--> c)
flipFL = returnFLF $ \f -> returnFLF $ \x -> returnFLF $ \y ->
  f `appFL` y `appFL` x

curryFL :: FL ((Tuple2FL FL a b :--> c) :--> a :--> b :--> c)
curryFL = returnFLF $ \f -> returnFLF $ \x -> returnFLF $ \y ->
  f `appFL` P.return (Tuple2FL x y)

uncurryFL :: FL ((a :--> b :--> c) :--> Tuple2FL FL a b :--> c)
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

-- | Lifted (++) function for lists
(++#) :: FL (ListFL FL a :--> ListFL FL a :--> ListFL FL a)
(++#) = returnFLF $ \xs -> returnFLF $ \ys ->
  xs P.>>= \case
    NilFL -> ys
    ConsFL a as -> P.return (ConsFL a ((++#) `appFL` as `appFL` ys))

-- | Lifted map function for lists
mapFL :: FL ((a :--> b) :--> ListFL FL a :--> ListFL FL b)
mapFL = returnFLF $ \f -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> P.return (ConsFL (f `appFL` a) (mapFL `appFL` f `appFL` as))

-- | Lifted concat function
concatFL :: FoldableFL t => FL (t (ListFL FL a) :--> ListFL FL a)
concatFL = foldrFL `appFL` (++#) `appFL` P.return NilFL

-- | Lifted concatMap function
concatMapFL :: FoldableFL t => FL ((a :--> ListFL FL b) :--> t a :--> ListFL FL b)
concatMapFL = returnFLF $ \f -> foldrFL `appFL` ((.#) `appFL` (++#) `appFL` f) `appFL` P.return NilFL

-- | Lifted takeWhile function for lists
takeWhileFL :: FL ((a :--> BoolFL FL) :--> ListFL FL a :--> ListFL FL a)
takeWhileFL = returnFLF $ \p -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> (p `appFL` a) P.>>= \case
      FalseFL -> P.return NilFL
      TrueFL -> P.return (ConsFL a (takeWhileFL `appFL` p `appFL` as))

-- | Lifted drop function for lists
dropFL :: FL (IntFL FL :--> ListFL FL a :--> ListFL FL a)
dropFL = returnFLF $ \n -> returnFLF $ \xs ->
  (<=#) `appFL` n `appFL` P.return (IntFL 0) P.>>= \case
    FalseFL -> xs P.>>= \case
      NilFL -> P.return NilFL
      ConsFL _ as -> dropFL `appFL` ((-#) `appFL` n `appFL` P.return (IntFL 1)) `appFL` as
    TrueFL -> xs

-- | Lifted maybe function
maybeFL :: FL (b :--> (a :--> b) :--> MaybeFL FL a :--> b)
maybeFL = returnFLF $ \n -> returnFLF $ \j -> returnFLF $ \m -> m P.>>= \case
  NothingFL -> n
  JustFL x -> j `appFL` x

-- | Lifted lookup function
lookupFL :: EqFL a => FL (a :--> ListFL FL (Tuple2FL FL a b) :--> MaybeFL FL b)
lookupFL = returnFLF $ \k -> returnFLF $ \xs -> xs P.>>= \case
  NilFL -> P.return NothingFL
  ConsFL y kvs -> y P.>>= \case
    Tuple2FL k2 v -> ((==#) `appFL` k `appFL` k2) P.>>= \case
      FalseFL -> lookupFL `appFL` k `appFL` kvs
      TrueFL -> P.return (JustFL v)

-- | Lifted notElem function
notElemFL :: (FoldableFL t, EqFL a) => FL (a :--> t a :--> BoolFL FL)
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

  stimes :: IntegralFL b => FL (b :--> a :--> a)
  --stimes = stimesDefault

{-instance SemigroupFL (ListFL FL a) where
  (<>#) = (++#)
  --stimesFL = stimesListFL-}

--TODO: Move
class SemigroupFL a => MonoidFL a where
  mempty  :: FL a

  mappend :: FL (a :--> a :--> a)
  mappend = (<>#)

  mconcat :: FL (ListFL FL a :--> a)
  --mconcat = foldr mappend mempty

--instance MonoidFL (ListFL FL a) where

--TODO: Move to BuiltIn.Foldable
class FoldableFL t where
    foldFL :: MonoidFL m => FL (t m :--> m)
    --foldFL = foldMapFL `appFL` idFL

    foldMapFL :: MonoidFL m => FL ((a :--> m) :--> t a :--> m)
    --foldMapFL = returnFLF $ \f -> foldrFL `appFL` ((.#) `appFL` mappendFL `appFL` f) `appFL` memptyFL

    foldMap'FL :: MonoidFL m => FL ((a :--> m) :--> t a :--> m)
    --foldMap'FL = returnFLF $ \f -> foldl'FL `appFL` (returnFLF $ \acc -> returnFLF $ \a -> (<>#) `appFL` acc `appFL` a) `appFL` memptyFL

    foldrFL :: FL ((a :--> b :--> b) :--> b :--> t a :--> b)
    --foldrFL f z t = appEndo (foldMap (Endo #. f) t) z

    foldr'FL :: FL ((a :--> b :--> b) :--> b :--> t a :--> b)
    --foldr' f z0 xs = foldl f' id xs z0
    --  where f' k x z = k $! f x z

    foldlFL :: FL ((b :--> a :--> b) :--> b :--> t a :--> b)
    --foldl f z t = appEndo (getDual (foldMap (Dual . Endo . flip f) t)) z

    foldl'FL :: FL ((b :--> a :--> b) :--> b :--> t a :--> b)
    --foldl'FL f z0 xs = foldr f' id xs z0
    --  where f' x k z = k $! f z x

    foldr1FL :: FL ((a :--> a :--> a) :--> t a :--> a)
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
  elemFL = returnFLF $ \x -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.return FalseFL
    ConsFL y ys -> ((==#) `appFL` x `appFL` y) P.>>= \case
      FalseFL -> elemFL `appFL` x `appFL` ys
      TrueFL -> P.return TrueFL
  foldlFL = returnFLF $ \f -> returnFLF $ \e -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> e
    ConsFL y ys -> foldlFL `appFL` f `appFL` (f `appFL` e `appFL` y) `appFL` ys
  foldl1FL = returnFLF $ \f -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> P.empty
    ConsFL y ys -> foldlFL `appFL` f `appFL` y `appFL` ys
  foldrFL = returnFLF $ \f -> returnFLF $ \e -> returnFLF $ \xs -> xs P.>>= \case
    NilFL -> e
    ConsFL y ys -> f `appFL` y `appFL` (foldrFL `appFL` f `appFL` e `appFL` ys)
  foldr1FL = returnFLF $ \f -> returnFLF $ \xs -> xs P.>>= \case
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

data BoolFL (m :: Type -> Type) = FalseFL | TrueFL

type instance Lifted m Bool = BoolFL m

instance HasPrimitiveInfo (BoolFL FL) where
  primitiveInfo = NoPrimitive

instance Narrowable (BoolFL FL) where
  narrow _ = [(FalseFL, 0), (TrueFL, 0)]

instance Convertible Bool where
  to False = FalseFL
  to True = TrueFL
  fromWith _ FalseFL = False
  fromWith _ TrueFL = True

instance Matchable Bool where
  match False FalseFL = P.return ()
  match True  TrueFL  = P.return ()
  match _     _       = P.empty

instance Unifiable Bool where
  lazyUnify FalseFL FalseFL = P.return ()
  lazyUnify TrueFL  TrueFL  = P.return ()
  lazyUnify _       _       = P.empty

instance NormalForm Bool where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree Bool where
  showFree' False = "False"
  showFree' True  = "True"

instance Invertible Bool

data UnitFL (m :: Type -> Type) = UnitFL

type instance Lifted m () = UnitFL m

instance HasPrimitiveInfo (UnitFL FL) where
  primitiveInfo = NoPrimitive

instance Narrowable (UnitFL FL) where
  narrow _ = [(UnitFL, 0)]

instance Convertible () where
  to () = UnitFL
  fromWith _ UnitFL = ()

instance Matchable () where
  match () UnitFL = P.return ()

instance Unifiable () where
  lazyUnify UnitFL UnitFL = P.return ()

instance NormalForm () where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree () where
  showFree' () = "()"

instance Invertible ()

data OrderingFL (m :: Type -> Type) = LTFL | EQFL | GTFL

type instance Lifted m Ordering = OrderingFL m

instance HasPrimitiveInfo (OrderingFL FL) where
  primitiveInfo = NoPrimitive

instance Narrowable (OrderingFL FL) where
  narrow _ = [(LTFL , 0), (EQFL, 0), (GTFL, 0)]

instance Convertible Ordering where
  to LT = LTFL
  to EQ = EQFL
  to GT = GTFL

  fromWith _ = \case
    LTFL -> LT
    EQFL -> EQ
    GTFL -> GT

instance Matchable Ordering where
  match LT LTFL = P.return ()
  match EQ EQFL = P.return ()
  match GT GTFL = P.return ()
  match _  _    = P.empty

instance Unifiable Ordering where
  lazyUnify LTFL LTFL = P.return ()
  lazyUnify EQFL EQFL = P.return ()
  lazyUnify GTFL GTFL = P.return ()
  lazyUnify _    _    = P.empty

instance NormalForm Ordering where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree Ordering where
  showFree' LT = "LT"
  showFree' EQ = "EQ"
  showFree' GT = "GT"

instance Invertible Ordering

instance HasPrimitiveInfo (IntegerFL FL) where
  primitiveInfo = Primitive

instance Convertible Integer where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Integer where
  match x y = P.guard (x P.== P.coerce y)

instance Unifiable Integer where
  lazyUnify (IntegerFL x) (IntegerFL y) = P.guard (x P.== y)

instance NormalForm Integer where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree Integer where
  showFree' = P.show

instance Invertible Integer

instance HasPrimitiveInfo (IntFL FL) where
  primitiveInfo = Primitive

instance Convertible Int where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Int where
  match i1 (IntFL i2) = P.guard (i1 P.== i2)

instance Unifiable Int where
  lazyUnify (IntFL x) (IntFL y) = P.guard (x P.== y)

instance NormalForm Int where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree Int where
  showFree' = P.show

instance Invertible Int

instance HasPrimitiveInfo (FloatFL FL) where
  primitiveInfo = Primitive

instance Convertible Float where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Float where
  match x y = P.guard (x P.== P.coerce y)

instance Unifiable Float where
  lazyUnify (FloatFL x) (FloatFL y) = P.guard (x P.== y)

instance NormalForm Float where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree Float where
  showFree' = P.show

instance Invertible Float

instance HasPrimitiveInfo (DoubleFL FL) where
  primitiveInfo = Primitive

instance Convertible Double where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Double where
  match x y = P.guard (x P.== P.coerce y)

instance Unifiable Double where
  lazyUnify (DoubleFL x) (DoubleFL y) = P.guard (x P.== y)

instance NormalForm Double where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance ShowFree Double where
  showFree' = P.show

instance Invertible Double

instance HasPrimitiveInfo (CharFL FL) where
  primitiveInfo = Primitive

instance Convertible P.Char where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable P.Char where
  match x y = P.guard (x P.== P.coerce y)

instance Unifiable P.Char where
  lazyUnify (CharFL x) (CharFL y) = P.guard (x P.== y)

instance NormalForm P.Char where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

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
  showFL = returnFLF $ \x -> apply2FL showsFL x (P.return NilFL)

  showListFL :: FL (ListFL FL a :--> ShowSFL FL)
  showListFL = returnFLF $ \ls -> returnFLF $ \s -> apply3FL showsList__ showsFL ls s

showsList__ :: FL ((a :--> ShowSFL FL) :--> ListFL FL a :--> ShowSFL FL)
showsList__ = returnFLF $ \showx -> returnFLF $ \list -> returnFLF $ \s ->
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
  showListFL = returnFLF $ \x -> FL $ groundNormalFormFL x P.>>= \v -> unFL (toFL (P.showList (fromIdentity v)))

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
  compareFL = returnFLF $ \a1 -> returnFLF $ \a2 ->
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
  maxFL = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL (>=#) a1 a2 P.>>= \case
      TrueFL -> a1
      _      -> a2

  minFL :: FL (a :--> a :--> a)
  minFL = returnFLF $ \a1 -> returnFLF $ \a2 ->
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

instance (OrdFL a) => OrdFL (ListFL FL a) where
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

  divModFL = returnFLF $ \n -> returnFLF $ \d ->
    let qr = apply2FL quotRemFL n d
    in qr P.>>= \(Tuple2FL q r) -> apply2FL (==#) (signumFL `appFL` r)
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
  fmapFL :: FL ((a :--> b) :--> f a :--> f b)
  (<$#) :: FL (a :--> f b :--> f a)
  (<$#) = returnFLF $ \a -> returnFLF $ \f ->
    apply2FL fmapFL (constFL `appFL` a) f

instance FunctorFL (ListFL FL) where
  fmapFL = returnFLF $ \f -> returnFLF $ \l -> l P.>>= \case
    NilFL       -> P.return NilFL
    ConsFL x xs -> P.return (ConsFL (f `appFL` x) (apply2FL fmapFL f xs))

(<$>#) :: FunctorFL f => FL ((a :--> b) :--> (f a :--> f b))
(<$>#) = fmapFL

type instance Lifted FL P.Applicative = ApplicativeFL
type instance Lifted FL (P.Applicative f) = ApplicativeFL (Lifted FL f)
-- | Lifted Applicative type class
class FunctorFL f => ApplicativeFL f where
  pureFL :: FL (a :--> f a)

  (<*>#) :: FL (f (a :--> b) :--> f a :--> f b)
  (<*>#) = returnFLF $ \f -> returnFLF $ \a ->
    apply3FL liftA2FL (liftFL1 P.id) f a

  liftA2FL :: FL ((a :--> b :--> c) :--> f a :--> f b :--> f c)
  liftA2FL = returnFLF $ \f -> returnFLF $ \a -> returnFLF $ \b ->
    apply2FL (<*>#) (apply2FL fmapFL f a) b

  (*>#) :: FL (f a :--> f b :--> f b)
  (*>#) = returnFLF $ \a -> returnFLF $ \b ->
    apply3FL liftA2FL (liftFL2 (P.const P.id)) a b

  (<*#) :: FL (f a :--> f b :--> f a)
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
  emptyFL :: FL (f a)
  (<|>#) :: FL (f a :--> f a :--> f a)
  someFL  :: FL (f a :--> f (ListFL FL a))
  someFL = returnFLF $ \v ->
    let many_v = apply2FL (<|>#) some_v (pureFL `appFL` P.return NilFL)
        some_v = apply3FL liftA2FL consFL v many_v
        consFL = returnFLF $ \x -> returnFLF $ \y -> P.return (ConsFL x y)
    in some_v
  manyFL  :: FL (f a :--> f (ListFL FL a))
  manyFL = returnFLF $ \v ->
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
  (>>=#) :: FL (m a :--> (a :--> m b) :--> m b)
  (>>#)  :: FL (m a :--> m b :--> m b)
  (>>#) = returnFLF $ \a -> returnFLF $ \b ->
    apply2FL (>>=#) a (returnFLF (P.const b))
  returnFL :: FL (a :--> m a)
  returnFL = pureFL
  {-# MINIMAL (>>=#) #-}

instance MonadFL (ListFL FL) where
  (>>=#) = returnFLF $ \a -> returnFLF $ \f -> a P.>>= \case
    NilFL       -> P.return NilFL
    ConsFL x xs -> apply2FL (++#) (f `appFL` x) (apply2FL (>>=#) xs f)

type instance Lifted FL P.MonadFail = MonadFailFL
type instance Lifted FL (P.MonadFail f) = MonadFailFL (Lifted FL f)
-- | Lifted MonadFail type class
class MonadFL m => MonadFailFL m where
  failFL :: FL (StringFL FL :--> m a)

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
    apply2FL mapFL toEnumFL (enumFromFL `appFL`
      (fromEnumFL `appFL` x1))

  enumFromThenFL   :: FL (a :--> a        :--> ListFL FL a)
  enumFromThenFL   = returnFLF $ \x1 -> returnFLF $ \x2 ->
    apply2FL mapFL toEnumFL (apply2FL enumFromThenFL
      (fromEnumFL `appFL` x1) (fromEnumFL `appFL` x2))

  enumFromToFL     :: FL (a        :--> a :--> ListFL FL a)
  enumFromToFL     = returnFLF $ \x1 ->                   returnFLF $ \x3 ->
    apply2FL mapFL toEnumFL (apply2FL enumFromToFL
      (fromEnumFL `appFL` x1)                         (fromEnumFL `appFL` x3))

  enumFromThenToFL :: FL (a :--> a :--> a :--> ListFL FL a)
  enumFromThenToFL = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    apply2FL mapFL toEnumFL (apply3FL enumFromThenToFL
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
      resolveFL x P.>>= \case
        Val a -> unFL $ P.return (coerce (f (coerce a)))
        x'    -> do
          j <- freshIdentifierND
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
      resolveFL x P.>>= \x' -> resolveFL y P.>>= \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ P.return $ coerce (coerce a `op` coerce b)
          _                  -> do
            j <- freshIdentifierND
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
primitiveOrd2 :: (a -> a -> Bool) -> P.Maybe (FLVal (Lifted FL a) -> FLVal (Lifted FL a) -> Constraint) -> FL (Lifted FL a :--> Lifted FL a :--> Lifted FL Bool)
primitiveOrd2 op mConstraint = returnFLF $ \x -> returnFLF $ \y ->
  case mConstraint of
    P.Just constraint -> FL $
      resolveFL x P.>>= \x' -> resolveFL y P.>>= \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ toFL $ coerce a `op` coerce b
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
primitive2Pair :: (Convertible a, Convertible b, Convertible c, Convertible d, HasPrimitiveInfo (Lifted FL c), HasPrimitiveInfo  (Lifted FL d)) => (a -> b -> (c, d)) -> P.Maybe (FLVal (Lifted FL a) -> FLVal (Lifted FL b) -> FLVal (Lifted FL c) -> FLVal (Lifted FL d) -> Constraint) -> FL (Lifted FL a :--> Lifted FL b :--> Lifted FL (c, d))
primitive2Pair op mConstraint = returnFLF $ \x -> returnFLF $ \y ->
  case mConstraint of
    P.Just constraint -> FL $
      resolveFL x P.>>= \x' -> resolveFL y P.>>= \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ toFL $ coerce a `op` coerce b
          _                  -> do
            j <- freshIdentifierND
            k <- freshIdentifierND
            assertConstraintND (constraint x' y' (Var j) (Var k)) (j : k : varsOf x' y')
            -- Diss: Checking consistency is unnecessary, because "j" and "k" are fresh.
            -- However, it is important to enter x and y in the set of constrained vars, because
            -- they might get constrained indirectly via "j". Example:
            -- j <- x + y
            -- j <- 1
            -- matchFL 9 x
            -- matchFL 0 y
            P.return (Val (Tuple2FL (free j) (free k)))
            where
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = []
    P.Nothing         -> apply2FL (liftFL2Convert op) x y
