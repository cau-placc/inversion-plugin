{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE NoStarIsType           #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UnboxedTuples          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -Wno-orphans        #-}
{-# OPTIONS_GHC -Wno-unused-foralls #-}
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
import qualified GHC.Int       as P
import qualified GHC.Stack     as P
import qualified Prelude       as P hiding (mapM)
import           GHC.Types (RuntimeRep, Type)
import           GHC.Int   (Int64(..), Int(..))
import           Unsafe.Coerce ( unsafeCoerce )
import           Prelude ( Bool (..), Double, Float, Integer, Ordering (..), ($) )
import           Data.Proxy
import           Plugin.Effect.Monad as M
import           Plugin.Effect.Util  as M
import           Plugin.Effect.TH
import           Plugin.Trans.TysWiredIn

-- * Lifted tuple types and internal instances

P.concat P.<$> P.mapM genLiftedTupleDataDeclAndInstances [2 .. maxTupleArity]

-- * Lifted list type and internal instances

data ListFL m a = NilFL | ConsFL (m a) (m (ListFL m a))

type StringFL m = ListFL m (CharFL m)

type instance Lifted m [] = ListFL m
type instance Lifted m [a] = ListFL m (Lifted m a)

instance HasPrimitiveInfo (ListFL FL a)

instance (Narrowable a, HasPrimitiveInfo a) => Narrowable (ListFL FL a) where
  narrow _ j _ = [(NilFL, 0), (ConsFL (freeFL j) (freeFL (j P.+ 1)), 2)]

instance (Convertible a) => Convertible [a] where
  to [] = NilFL
  to (x : xs) = ConsFL (toFL x) (toFL xs)
  from NilFL = []
  from (ConsFL x xs) = fromFL x : fromFL xs

instance (Convertible a, Matchable a, HasPrimitiveInfo (Lifted FL a)) => Matchable [a] where
  match [] NilFL = P.return ()
  match (x : xs) (ConsFL y ys) = matchFL x y P.>> matchFL xs ys
  match _ _ = P.empty

instance NF a => NF (ListFL FL a) where
  nf f = \case
      NilFL -> P.return NilFL
      ConsFL x xs ->
        f x P.>>= \y ->
          f xs P.>>= \ys ->
            P.return (ConsFL (P.return y) (P.return ys))

instance Invertible a => Invertible [a]

data RatioFL m a = m a :%# m a

type instance Lifted m P.Ratio = RatioFL m
type instance Lifted m (P.Ratio a) = RatioFL m (Lifted m a)

instance (Narrowable a, HasPrimitiveInfo a) => Narrowable (RatioFL FL a) where
  narrow _ j _ = [(freeFL j :%# freeFL (j P.+ 1), 2)]

instance (Convertible a) => Convertible (P.Ratio a) where
  to (a P.:% b) = toFL a :%# toFL b
  from (a :%# b) = fromFL a P.:% fromFL b

instance (Convertible a, Matchable a, HasPrimitiveInfo (Lifted FL a)) => Matchable (P.Ratio a) where
  match (a P.:% b) (x :%# y) = matchFL a x P.>> matchFL b y

type RationalFL m = RatioFL m (IntegerFL m)

-- * For plugin purposes only.

failFLStr :: P.String -> a
failFLStr = P.error

failFLStrFL :: FL (StringFL FL :--> a)
failFLStrFL = P.return $ Func $ P.const P.empty

-- Lifted seq operator to force evaluation. Forces the effect and value.
seq :: forall (k :: RuntimeRep) a b. a -> b -> b
seq = P.seq

seqFL :: forall (k :: RuntimeRep) a b. (Narrowable a, HasPrimitiveInfo a)
      => FL (FL a -> FL (FL b -> FL b))
seqFL = P.return $ \a -> P.return $ \b ->
  a P.>>= \a' -> P.seq a' b

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
eqStringFL = liftFL1Convert (P.==)

-- | Lifted equality test for characters
eqChar :: P.Char -> P.Char -> Bool
eqChar = (P.==)

-- | Lifted equality test for strings
eqCharFL :: FL (CharFL FL :--> CharFL FL :--> BoolFL FL)
eqCharFL = liftFL1Convert (P.==)

(<##) :: FL (IntFL FL :--> IntFL FL :--> IntFL FL)
(<##) = liftFL1Convert op
  where
    op (I# i1) (I# i2) = I# (i1 P.<# i2)

(==##) :: FL (IntFL FL :--> IntFL FL :--> IntFL FL)
(==##) = liftFL1Convert op
  where
    op (I# i1) (I# i2) = I# (i1 P.==# i2)

-- * Prelude stuff

undefinedFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . P.HasCallStack => FL a
undefinedFL = P.empty

errorFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . P.HasCallStack => FL (StringFL FL :--> a)
errorFL = failFLStrFL

notFL :: FL (BoolFL FL :--> BoolFL FL)
notFL = liftFL1Convert P.not

idFL :: FL (a :--> a)
idFL = returnFLF P.id

(.#) :: FL ((b :--> c) :--> (a :--> b) :--> a :--> c)
(.#) = returnFLF $ \f -> returnFLF $ \g -> returnFLF $ \a ->
  f `appFL` (g `appFL` a)

-- | Lifted const function
constFL :: FL (a :--> b :--> a)
constFL = returnFLF $ \a -> returnFLF $ P.const a

-- | Lifted logical and
(&&#) :: FL (BoolFL FL :--> BoolFL FL :--> BoolFL FL)
(&&#) = liftFL2Convert (P.&&)

-- | Lifted append function for lists
appendFL :: FL (ListFL FL a :--> ListFL FL a:--> ListFL FL a)
appendFL = returnFLF $ \xs -> returnFLF $ \ys ->
  xs P.>>= \case
    NilFL -> ys
    ConsFL a as -> P.return (ConsFL a (appendFL `appFL` as `appFL` ys))

-- | Lifted concatMap function for lists
concatMapFL :: FL ((a :--> ListFL FL b) :--> ListFL FL a :--> ListFL FL b)
concatMapFL = returnFLF $ \f -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> appendFL `appFL` (f `appFL` a) `appFL` (concatMapFL `appFL` f `appFL` as)

-- | Lifted map function for lists
mapFL :: FL ((a :--> b) :--> ListFL FL a :--> ListFL FL b)
mapFL = returnFLF $ \f -> returnFLF $ \xs ->
  xs P.>>= \case
    NilFL -> P.return NilFL
    ConsFL a as -> P.return (ConsFL (f `appFL` a) (mapFL `appFL` f `appFL` as))

newtype BoolFL (m :: Type -> Type) = BoolFL Bool

type instance Lifted m Bool = BoolFL m

instance HasPrimitiveInfo (BoolFL FL)

instance Narrowable (BoolFL FL) where
  narrow _ _ _ = P.coerce [(False, 0 :: Integer), (True, 0)]

instance Convertible Bool where
  to = P.coerce
  from = P.coerce

instance Matchable Bool where
  match x y = P.guard (x P.== P.coerce y)

instance NF (BoolFL FL)

instance Invertible Bool

newtype UnitFL (m :: Type -> Type) = UnitFL ()

type instance Lifted m () = UnitFL m

instance HasPrimitiveInfo (UnitFL FL)

instance Narrowable (UnitFL FL) where
  narrow _ _ _ = P.coerce [((), 0 :: Integer)]

instance Convertible () where
  to = P.coerce
  from = P.coerce

instance Matchable () where
  match x y = P.guard (x P.== P.coerce y)

instance NF (UnitFL FL)

instance Invertible ()

newtype OrderingFL (m :: Type -> Type) = OrderingFL Ordering

type instance Lifted m Ordering = OrderingFL m

instance HasPrimitiveInfo (OrderingFL FL)

instance Narrowable (OrderingFL FL) where
  narrow _ _ _ = P.coerce [(LT , 0 :: Integer), (EQ, 0), (GT, 0)]

instance Convertible Ordering where
  to = P.coerce
  from = P.coerce

instance Matchable Ordering where
  match x y = P.guard (x P.== P.coerce y)

instance NF (OrderingFL FL)

instance Invertible Ordering

newtype IntegerFL (m :: Type -> Type) = IntegerFL Integer

type instance Lifted m Integer = IntegerFL m

instance HasPrimitiveInfo (IntegerFL FL) where
  primitiveInfo = Primitive (Proxy @(IntegerFL FL, Integer))

instance Narrowable (IntegerFL FL) where
  narrow = narrowPrimitive @(IntegerFL FL) @Integer

instance Convertible Integer where
  to = P.coerce
  from = P.coerce

instance Matchable Integer where
  match x y = P.guard (x P.== P.coerce y)

instance NF (IntegerFL FL)

instance Invertible Integer

newtype IntFL (m :: Type -> Type) = IntFL P.Int64

type instance Lifted m Int = IntFL m

instance HasPrimitiveInfo (IntFL FL) where
  primitiveInfo = Primitive (Proxy @(IntFL FL, P.Int64))

instance Narrowable (IntFL FL) where
  narrow = narrowPrimitive @(IntFL FL) @P.Int64

instance Convertible Int where
  to (I# i) = IntFL (I64# i)
  from (IntFL (I64# i)) = I# i

instance Matchable Int where
  match (I# i1) (IntFL (I64# i2)) = P.guard (I# i1 P.== I# i2)

instance NF (IntFL FL)

instance Invertible Int

newtype FloatFL (m :: Type -> Type) = FloatFL Float

type instance Lifted m Float = FloatFL m

instance HasPrimitiveInfo (FloatFL FL) where
  primitiveInfo = Primitive (Proxy @(FloatFL FL, Float))

instance Narrowable (FloatFL FL) where
  narrow = narrowPrimitive @(FloatFL FL) @Float

instance Convertible Float where
  to = P.coerce
  from = P.coerce

instance Matchable Float where
  match x y = P.guard (x P.== P.coerce y)

instance NF (FloatFL FL)

instance Invertible Float

newtype DoubleFL (m :: Type -> Type) = DoubleFL Double

type instance Lifted m Double = DoubleFL m

instance HasPrimitiveInfo (DoubleFL FL) where
  primitiveInfo = Primitive (Proxy @(DoubleFL FL, Double))

instance Narrowable (DoubleFL FL) where
  narrow = narrowPrimitive @(DoubleFL FL) @Double

instance Convertible Double where
  to = P.coerce
  from = P.coerce

instance Matchable Double where
  match x y = P.guard (x P.== P.coerce y)

instance NF (DoubleFL FL)

instance Invertible Double

newtype CharFL (m :: Type -> Type) = CharFL P.Char

type instance Lifted m P.Char = CharFL m

instance HasPrimitiveInfo (CharFL FL) where
  primitiveInfo = Primitive (Proxy @(CharFL FL, P.Char))

instance Narrowable (CharFL FL) where
  narrow = narrowPrimitive @(CharFL FL) @P.Char

instance Convertible P.Char where
  to = P.coerce
  from = P.coerce

instance Matchable P.Char where
  match x y = P.guard (x P.== P.coerce y)

instance NF (CharFL FL)

instance Invertible P.Char


-- | Lifted ShowS type
type ShowSFL m = (-->) m (StringFL m) (StringFL m)

-- | Lifted Show type class
class ShowFL a where
  {-# MINIMAL showsPrec | show #-}
  showsPrec :: FL (IntFL FL :--> a :--> ShowSFL FL)
  showsPrec = returnFLF $ \_ -> returnFLF $ \x -> returnFLF $ \s ->
    apply2FL appendFL (show `appFL` x) s

  show :: FL (a :--> StringFL FL)
  show = returnFLF $ \x -> apply2FL shows x (P.return NilFL)

  showList :: FL (ListFL FL a :--> ShowSFL FL)
  showList = returnFLF $ \ls -> returnFLF $ \s -> apply3FL showsList__ shows ls s

showsList__ :: FL ((a :--> ShowSFL FL) :--> ListFL FL a :--> ShowSFL FL)
showsList__ = returnFLF $ \showx -> returnFLF $ \list -> returnFLF $ \s ->
  list P.>>= \case
    NilFL       -> apply2FL appendFL (toFL "[]") s
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

shows :: ShowFL a => FL (a :--> ShowSFL FL)
shows = showsPrec `appFL` toFL 0

showString :: FL (StringFL FL :--> ShowSFL FL)
showString = appendFL

showCommaSpace :: FL (ShowSFL FL)
showCommaSpace = showString `appFL` toFL ", "

showSpace :: FL (ShowSFL FL)
showSpace =  showString `appFL` toFL " "

showParen :: FL (BoolFL FL :--> ShowSFL FL :--> ShowSFL FL)
showParen = returnFLF $ \b -> returnFLF $ \s -> b P.>>= \case
  BoolFL True  -> apply2FL (.#) (showString `appFL` toFL "(")
          (apply2FL (.#) s (showString `appFL` toFL ")"))
  BoolFL False -> s

instance ShowFL (BoolFL FL) where
  show = liftFL1Convert P.show

instance ShowFL (UnitFL FL) where
  show = liftFL1Convert P.show

instance ShowFL (IntFL FL) where
  show = liftFL1Convert P.show

instance ShowFL (IntegerFL FL) where
  show = liftFL1Convert P.show

instance ShowFL (FloatFL FL) where
  show = liftFL1Convert P.show

instance ShowFL (DoubleFL FL) where
  show = liftFL1Convert P.show

instance ShowFL (CharFL FL) where
  show = liftFL1Convert P.show
  showList = liftFL1Convert P.showList

instance ShowFL a => ShowFL (ListFL FL a) where
  show = returnFLF $ \xs -> apply2FL showList xs (P.return NilFL)


-- * Lifted Eq type class, instances and functions

-- | Lifted Eq type class
class EqFL a where
  (==) :: FL (a :--> a :--> BoolFL FL)
  (==) = returnFLF $ \a1 -> returnFLF $ \a2 -> notFL `appFL` apply2FL(/=) a1 a2

  (/=) :: FL (a :--> a :--> BoolFL FL)
  (/=) = returnFLF $ \a1 -> returnFLF $ \a2 -> notFL `appFL` apply2FL(==) a1 a2

instance EqFL (BoolFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL (UnitFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL (IntFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL (IntegerFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL (FloatFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL (DoubleFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL (CharFL FL) where
  (==) = liftFL2Convert (P.==)
  (/=) = liftFL2Convert (P./=)

instance EqFL a => EqFL (ListFL FL a) where
  (==) = returnFLF $ \a1 -> returnFLF $ \a2 -> a1 P.>>= \case
    NilFL       -> a2 P.>>= \case
      NilFL       -> P.return $ BoolFL True
      ConsFL _ _  -> P.return $ BoolFL False
    ConsFL x xs -> a2 P.>>= \case
      NilFL       -> P.return $ BoolFL False
      ConsFL y ys -> eqOn2 x y xs ys

instance EqFL a => EqFL (RatioFL FL a) where
  (==) = returnFLF $ \x1 -> returnFLF $ \x2 -> do
    (a1 :%# b1) <- x1
    (a2 :%# b2) <- x2
    eqOn2 a1 a2 b1 b2

eqOn2 :: (EqFL a1, EqFL a2)
      => FL a1 -> FL a1 -> FL a2 -> FL a2 -> FL (BoolFL FL)
eqOn2 x y xs ys = apply2FL (&&#) (apply2FL(==) x y) (apply2FL(==) xs ys)

-- * Lifted Ord type class, instances and functions

-- | Lifted Ord type class
class EqFL a => OrdFL a where
  {-# MINIMAL compare | (<=) #-}
  compare :: FL (a :--> a :--> OrderingFL FL)
  compare = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL(==) a1 a2 P.>>= \(BoolFL b1) -> if b1
      then P.return (OrderingFL EQ)
      else apply2FL(<=) a1 a2 P.>>= \(BoolFL b2) -> if b2
        then P.return $ OrderingFL LT
        else P.return $ OrderingFL GT

  (<) :: FL (a :--> a :--> BoolFL FL)
  (<) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compare a1 a2 P.>>= \case
      OrderingFL LT -> P.return $ BoolFL True
      _             -> P.return $ BoolFL False

  (<=) :: FL (a :--> a :--> BoolFL FL)
  (<=) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compare a1 a2 P.>>= \case
      OrderingFL GT -> P.return $ BoolFL False
      _             -> P.return $ BoolFL True

  (>) :: FL (a :--> a :--> BoolFL FL)
  (>) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compare a1 a2 P.>>= \case
      OrderingFL GT -> P.return $ BoolFL True
      _             -> P.return $ BoolFL False

  (>=) :: FL (a :--> a :--> BoolFL FL)
  (>=) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL compare a1 a2 P.>>= \case
      OrderingFL LT -> P.return $ BoolFL False
      _             -> P.return $ BoolFL True

  max :: FL (a :--> a :--> a)
  max = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL(>=) a1 a2 P.>>= \case
      BoolFL True -> a1
      _           -> a2

  min :: FL (a :--> a :--> a)
  min = returnFLF $ \a1 -> returnFLF $ \a2 ->
    apply2FL(<=) a1 a2 P.>>= \case
      BoolFL True -> a1
      _           -> a2

instance OrdFL (BoolFL FL) where
  compare = liftFL2Convert P.compare

instance OrdFL (UnitFL FL) where
  compare = liftFL2Convert P.compare

instance OrdFL (IntFL FL) where
  compare = liftFL2Convert P.compare

instance OrdFL (IntegerFL FL) where
  compare = liftFL2Convert P.compare

instance OrdFL (FloatFL FL) where
  compare = liftFL2Convert P.compare

instance OrdFL (DoubleFL FL) where
  compare = liftFL2Convert P.compare

instance (OrdFL a) => OrdFL (ListFL FL a) where
  compare = returnFLF $ \x -> returnFLF $ \y ->
    x P.>>= \x' -> y P.>>= \y' -> case (x', y') of
      (NilFL      , NilFL      ) -> P.return (OrderingFL EQ)
      (NilFL      , ConsFL _ _ ) -> P.return (OrderingFL LT)
      (ConsFL _ _ , NilFL      ) -> P.return (OrderingFL GT)
      (ConsFL a as, ConsFL b bs) -> apply2FL compare a b P.>>= \case
        OrderingFL EQ -> apply2FL compare as bs
        o  -> P.return o

-- * Lifted Num type class, instances and functions

-- | Lifted Num type class
class NumFL a where
  (+) :: FL (a :--> a :--> a)
  (-) :: FL (a :--> a :--> a)
  (-) = returnFLF $ \a -> returnFLF $ \b ->
    (+) `appFL` a `appFL` (negate `appFL` b)
  (*) :: FL (a :--> a :--> a)
  negate :: FL (a :--> a)
  negate = returnFLF $ \a -> (-) `appFL` (fromInteger `appFL` toFL 0) `appFL` a
  abs    :: FL (a :--> a)
  signum :: FL (a :--> a)
  fromInteger :: FL (IntegerFL FL :--> a)

instance NumFL (IntFL FL) where
  (+) = liftFL2Convert (P.+)
  (-) = liftFL2Convert (P.-)
  (*) = liftFL2Convert (P.*)
  negate = liftFL1Convert P.negate
  abs    = liftFL1Convert P.abs
  signum = liftFL1Convert P.signum
  fromInteger = liftFL1Convert P.fromInteger

instance NumFL (IntegerFL FL) where
  (+) = liftFL2Convert (P.+)
  (-) = liftFL2Convert (P.-)
  (*) = liftFL2Convert (P.*)
  negate = liftFL1Convert P.negate
  abs    = liftFL1Convert P.abs
  signum = liftFL1Convert P.signum
  fromInteger = liftFL1Convert P.fromInteger

instance NumFL (FloatFL FL) where
  (+) = liftFL2Convert (P.+)
  (-) = liftFL2Convert (P.-)
  (*) = liftFL2Convert (P.*)
  negate = liftFL1Convert P.negate
  abs    = liftFL1Convert P.abs
  signum = liftFL1Convert P.signum
  fromInteger = liftFL1Convert P.fromInteger

instance NumFL (DoubleFL FL) where
  (+) = liftFL2Convert (P.+)
  (-) = liftFL2Convert (P.-)
  (*) = liftFL2Convert (P.*)
  negate = liftFL1Convert P.negate
  abs    = liftFL1Convert P.abs
  signum = liftFL1Convert P.signum
  fromInteger = liftFL1Convert P.fromInteger

-- * Lifted Fractional type class, instances and functions

-- | Lifted Fractional type class
class NumFL a => FractionalFL a where
  {-# MINIMAL fromRational, (recip | (/)) #-}

  (/) :: FL (a :--> a :--> a)
  (/) = returnFLF $ \x -> returnFLF $ \y -> apply2FL(*) x  (recip `appFL` y)

  recip :: FL (a :--> a)
  recip = returnFLF $ \x -> apply2FL(/) (fromInteger `appFL` toFL 1) x

  fromRational :: FL (RationalFL FL :--> a)

instance FractionalFL (FloatFL FL) where
  (/) = liftFL2Convert (P./)
  fromRational = liftFL1Convert P.fromRational

instance FractionalFL (DoubleFL FL) where
  (/) = liftFL2Convert (P./)
  fromRational = liftFL1Convert P.fromRational

-- * Lifted Real type class, instances and functions

-- | Lifted Real type class
class (NumFL a, OrdFL a) => RealFL a where
  toRational :: FL (a :--> RationalFL FL)

instance RealFL (IntFL FL) where
  toRational = liftFL1Convert P.toRational

instance RealFL (IntegerFL FL) where
  toRational = liftFL1Convert P.toRational

instance RealFL (FloatFL FL) where
  toRational = liftFL1Convert P.toRational

instance RealFL (DoubleFL FL) where
  toRational = liftFL1Convert P.toRational

-- * Lifted Integral type class, instances and functions

-- | Lifted Integral type class
class (RealFL a, EnumFL a) => IntegralFL a where
  quot      :: FL (a :--> a :--> a)
  rem       :: FL (a :--> a :--> a)
  div       :: FL (a :--> a :--> a)
  mod       :: FL (a :--> a :--> a)
  --quotRem   :: FL (a :--> a :--> Tuple2ND FL a a)
  --divMod    :: FL (a :--> a :--> Tuple2ND FL a a)
  toInteger :: FL (a :--> IntegerFL FL)

  -- quot   = returnFLF $ \n -> returnFLF $ \d -> fst `appFL` apply2FLquotRem n d
  -- rem    = returnFLF $ \n -> returnFLF $ \d -> snd `appFL` apply2FLquotRem n d
  -- div    = returnFLF $ \n -> returnFLF $ \d -> fst `appFL` apply2FLdivMod n d
  -- mod    = returnFLF $ \n -> returnFLF $ \d -> snd `appFL` apply2FLdivMod n d

  -- This default implementation is replaced at compile-time with divModDefault
  -- divMod = returnFLF $ \n -> returnFLF $ \d ->
  --   let qr = apply2FLquotRem n d
  --   in qr P.>>= \(Tuple2 q r) -> apply2FL(==) (signum `appFL` r)
  --                                           (negate `appFL` (signum `appFL` d))
  --         P.>>= \(BoolFL b) -> if b
  --           then P.return (Tuple2 (apply2FL(-) q
  --                                   (fromInteger `appFL` (liftE (P.return 1))))
  --                                   (apply2FL(+) r d))
  --           else qr

instance IntegralFL (IntFL FL) where
  quot = liftFL2Convert P.quot
  rem  = liftFL2Convert P.rem
  div  = liftFL2Convert P.div
  mod  = liftFL2Convert P.mod

  -- quotRem = returnFLF $ \a1 -> returnFLF $ \a2 -> do
  --   IntFL v1 <- a1
  --   IntFL v2 <- a2
  --   liftE (P.return (P.quotRem v1 v2))
  -- divMod = returnFLF $ \a1 -> returnFLF $ \a2 -> do
  --   IntFL v1 <- a1
  --   IntFL v2 <- a2
  --   liftE (P.return (P.divMod v1 v2))

  toInteger = liftFL1Convert P.toInteger

instance IntegralFL (IntegerFL FL) where
  quot = liftFL2Convert P.quot
  rem  = liftFL2Convert P.rem
  div  = liftFL2Convert P.div
  mod  = liftFL2Convert P.mod

  -- quotRem = returnFLF $ \a1 -> returnFLF $ \a2 -> do
  --   IntegerFL v1 <- a1
  --   IntegerFL v2 <- a2
  --   liftE (P.return (P.quotRem v1 v2))
  -- divMod = returnFLF $ \a1 -> returnFLF $ \a2 -> do
  --   IntegerFL v1 <- a1
  --   IntegerFL v2 <- a2
  --   liftE (P.return (P.divMod v1 v2))

  toInteger = returnFLF P.id

-- * Lifted Monad & Co type classes and instances

infixl 1 >>=, >>
infixl 4 <$, <*, *>, <*>
-- | Lifted Functor type class
class FunctorFL f where
  fmap :: FL ((a :--> b) :--> f a :--> f b)
  (<$) :: FL (a :--> f b :--> f a)
  (<$) = returnFLF $ \a -> returnFLF $ \f ->
    apply2FL fmap (constFL `appFL` a) f

instance FunctorFL (ListFL FL) where
  fmap = returnFLF $ \f -> returnFLF $ \l -> l P.>>= \case
    NilFL       -> P.return NilFL
    ConsFL x xs -> P.return (ConsFL (f `appFL` x) (apply2FL fmap f xs))

-- | Lifted Applicative type class
class FunctorFL f => ApplicativeFL f where
  pure :: FL (a :--> f a)

  (<*>) :: FL (f (a :--> b) :--> f a :--> f b)
  (<*>) = returnFLF $ \f -> returnFLF $ \a ->
    apply3FL liftA2 (liftFL1 P.id) f a

  liftA2 :: FL ((a :--> b :--> c) :--> f a :--> f b :--> f c)
  liftA2 = returnFLF $ \f -> returnFLF $ \a -> returnFLF $ \b ->
    apply2FL(<*>) (apply2FL fmap f a) b

  (*>) :: FL (f a :--> f b :--> f b)
  (*>) = returnFLF $ \a -> returnFLF $ \b ->
    apply3FL liftA2 (liftFL2 (P.const P.id)) a b

  (<*) :: FL (f a :--> f b :--> f a)
  (<*) = returnFLF $ \a -> returnFLF $ \b ->
    apply3FL liftA2 constFL a b
  {-# MINIMAL pure, ((<*>) | liftA2) #-}

instance ApplicativeFL (ListFL FL) where
  pure = returnFLF $ \a -> P.return (ConsFL a (P.return NilFL))
  (<*>) = returnFLF $ \fs -> returnFLF $ \as ->
    apply2FL concatMapFL (returnFLF $ \a ->
    apply2FL fmap      (returnFLF $ \f -> f `appFL` a) fs) as

  -- | Lifted Alternative type class
class ApplicativeFL f => AlternativeFL f where
  empty :: FL (f a)
  (<|>) :: FL (f a :--> f a :--> f a)
  some  :: FL (f a :--> f (ListFL FL a))
  some = returnFLF $ \v ->
    let many_v = apply2FL (<|>) some_v (pure `appFL` P.return NilFL)
        some_v = apply3FL liftA2 consFL v many_v
        consFL = returnFLF $ \x -> returnFLF $ \y -> P.return (ConsFL x y)
    in some_v
  many  :: FL (f a :--> f (ListFL FL a))
  many = returnFLF $ \v ->
    let many_v = apply2FL (<|>) some_v (pure `appFL` P.return NilFL)
        some_v = apply3FL liftA2 consFL v many_v
        consFL = returnFLF $ \x -> returnFLF $ \y -> P.return (ConsFL x y)
    in many_v

instance AlternativeFL (ListFL FL) where
  empty = P.return NilFL
  (<|>) = appendFL

-- | Lifted Monad type class
class ApplicativeFL m => MonadFL m where
  (>>=) :: FL (m a :--> (a :--> m b) :--> m b)
  (>>)  :: FL (m a :--> m b :--> m b)
  (>>) = returnFLF $ \a -> returnFLF $ \b ->
    apply2FL(>>=) a (returnFLF (P.const b))
  return :: FL (a :--> m a)
  return = pure
  {-# MINIMAL (>>=) #-}

instance MonadFL (ListFL FL) where
  (>>=) = returnFLF $ \a -> returnFLF $ \f -> a P.>>= \case
    NilFL       -> P.return NilFL
    ConsFL x xs -> apply2FL appendFL (f `appFL` x) (apply2FL(>>=) xs f)

-- | Lifted MonadFail type class
class MonadFL m => MonadFailFL m where
  fail :: FL (StringFL FL :--> m a)

instance MonadFailFL (ListFL FL) where
  fail = returnFLF $ \_ -> P.return NilFL

-- * Lifted Enum type class, instances and functions

-- | Lifted Enum type class
class EnumFL a where
  succ :: FL (a :--> a)
  succ = returnFLF $ \a ->
    toEnum `appFL` apply2FL(+) (toFL 1) (fromEnum `appFL` a)
  pred :: FL (a :--> a)
  pred = returnFLF $ \a ->
    toEnum `appFL` apply2FL(-) (toFL 1) (fromEnum `appFL` a)

  toEnum   :: FL (IntFL FL :--> a)
  fromEnum :: FL (a :--> IntFL FL)

  enumFrom       :: FL (a               :--> ListFL FL a)
  enumFrom       = returnFLF $ \x1 ->
    apply2FL mapFL toEnum (enumFrom `appFL`
      (fromEnum `appFL` x1))

  enumFromThen   :: FL (a :--> a        :--> ListFL FL a)
  enumFromThen   = returnFLF $ \x1 -> returnFLF $ \x2 ->
    apply2FL mapFL toEnum (apply2FL enumFromThen
      (fromEnum `appFL` x1) (fromEnum `appFL` x2))

  enumFromTo     :: FL (a        :--> a :--> ListFL FL a)
  enumFromTo     = returnFLF $ \x1 ->                   returnFLF $ \x3 ->
    apply2FL mapFL toEnum (apply2FL enumFromTo
      (fromEnum `appFL` x1)                      (fromEnum `appFL` x3))

  enumFromThenTo :: FL (a :--> a :--> a :--> ListFL FL a)
  enumFromThenTo = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    apply2FL mapFL toEnum (apply3FL enumFromThenTo
      (fromEnum `appFL` x1) (fromEnum `appFL` x2) (fromEnum `appFL` x3))

instance EnumFL (IntFL FL) where
  succ = (+) `appFL` toFL 1
  pred = (-) `appFL` toFL 1

  toEnum   = returnFLF P.id
  fromEnum = returnFLF P.id

  enumFrom = returnFLF $ \x1 ->
    x1 P.>>= \(IntFL v1) ->
    toFL (P.map P.fromIntegral (P.enumFrom v1))

  enumFromThen = returnFLF $ \x1 -> returnFLF $ \x2 ->
    x1 P.>>= \(IntFL v1) -> x2 P.>>= \(IntFL v2) ->
    toFL (P.map P.fromIntegral (P.enumFromThen v1 v2))

  enumFromTo = returnFLF $ \x1 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntFL v1) -> x3 P.>>= \(IntFL v3) ->
    toFL (P.map P.fromIntegral (P.enumFromTo v1 v3))

  enumFromThenTo = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntFL v1) -> x2 P.>>= \(IntFL v2) -> x3 P.>>= \(IntFL v3) ->
    toFL (P.map P.fromIntegral (P.enumFromThenTo v1 v2 v3))

instance EnumFL (IntegerFL FL) where
  succ = (+) `appFL` toFL 1
  pred = (-) `appFL` toFL 1

  toEnum   = toInteger
  fromEnum = fromInteger

  enumFrom = returnFLF $ \x1 ->
    x1 P.>>= \(IntegerFL v1) ->
    toFL (P.enumFrom v1)

  enumFromThen = returnFLF $ \x1 -> returnFLF $ \x2 ->
    x1 P.>>= \(IntegerFL v1) -> x2 P.>>= \(IntegerFL v2) ->
    toFL (P.enumFromThen v1 v2)

  enumFromTo = returnFLF $ \x1 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntegerFL v1) -> x3 P.>>= \(IntegerFL v3) ->
    toFL (P.enumFromTo v1 v3)

  enumFromThenTo = returnFLF $ \x1 -> returnFLF $ \x2 -> returnFLF $ \x3 ->
    x1 P.>>= \(IntegerFL v1) -> x2 P.>>= \(IntegerFL v2) -> x3 P.>>= \(IntegerFL v3) ->
    toFL (P.enumFromThenTo v1 v2 v3)

-- * Lifted Bounded type class, instances and functions

-- | Lifted Bounded type class
class BoundedFL a where
  minBound :: FL a
  maxBound :: FL a

instance BoundedFL (IntFL FL) where
  minBound = toFL P.minBound
  maxBound = toFL P.maxBound

class IsStringFL a where
  fromString :: FL (StringFL FL :--> a)

instance (a ~ CharFL FL) => IsStringFL (ListFL FL a) where
  fromString = returnFLF P.id
