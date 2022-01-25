{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
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

import qualified Control.Monad.State as S
import qualified Control.Monad as P
import qualified GHC.Base      as P hiding (mapM)
import qualified GHC.Real      as P
import qualified GHC.Stack     as P
import qualified GHC.Exts      as P
import qualified Prelude       as P hiding (mapM)
import           GHC.Types (RuntimeRep, Type)
import           GHC.Int   (Int(..))
import           Unsafe.Coerce ( unsafeCoerce )
import           Prelude ( Bool (..), Double, Float, Integer, Ordering (..), ($) )
import           Data.SBV (SBool, SBV, sNot, (.===), (./==), (.>), (.<), (.<=), (.>=), SDivisible(..))
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

instance HasPrimitiveInfo [a]

instance (Narrowable a) => Narrowable (ListFL FL a) where
  narrow _ j _ = [(NilFL, P.Left 0), (ConsFL (freeFL j) (freeFL (j P.+ 1)), P.Left 2)]

instance (Convertible a) => Convertible [a] where
  to [] = NilFL
  to (x : xs) = ConsFL (toFL x) (toFL xs)
  fromWith _ NilFL = []
  fromWith ff (ConsFL x xs) = ff x : ff xs

instance (Convertible a, Matchable a, HasPrimitiveInfo a) => Matchable [a] where
  match [] NilFL = P.return ()
  match (x : xs) (ConsFL y ys) = matchFL x y P.>> matchFL xs ys
  match _ _ = P.empty

instance NF a a' => NF [a] (ListFL FL a') where
  normalFormWith nf = \case
      NilFL -> P.return (P.pure NilFL)
      ConsFL x xs ->
        nf x P.>>= \y ->
          nf xs P.>>= \ys ->
            P.return (P.pure (ConsFL y ys))

instance Invertible a => Invertible [a]

data RatioFL m a = m a :%# m a

type instance Lifted m P.Ratio = RatioFL m
type instance Lifted m (P.Ratio a) = RatioFL m (Lifted m a)

instance HasPrimitiveInfo (P.Ratio a)

instance (Narrowable a) => Narrowable (RatioFL FL a) where
  narrow _ j _ = [(freeFL j :%# freeFL (j P.+ 1), P.Left 2)]

instance (Convertible a) => Convertible (P.Ratio a) where
  to (a P.:% b) = toFL a :%# toFL b
  fromWith ff (a :%# b) = ff a P.:% ff b

instance (Convertible a, Matchable a, HasPrimitiveInfo a) => Matchable (P.Ratio a) where
  match (a P.:% b) (x :%# y) = matchFL a x P.>> matchFL b y

instance NF a a' => NF (P.Ratio a) (RatioFL FL a') where
   normalFormWith nf = \case
       a :%# b ->
         nf a P.>>= \x ->
           nf b P.>>= \y ->
             P.return (P.pure (x :%# y))

type RationalFL m = RatioFL m (IntegerFL m)

-- * For plugin purposes only.

failFLStr :: P.String -> a
failFLStr = P.error

failFLStrFL :: FL (StringFL FL :--> a)
failFLStrFL = P.return $ Func $ P.const P.empty

-- Lifted seq operator to force evaluation. Forces the effect and value.
seq :: forall (k :: RuntimeRep) a b. a -> b -> b
seq = P.seq

seqFL :: forall (k :: RuntimeRep) a b. FL (FL a -> FL (FL b -> FL b))
seqFL = P.return $ \a -> P.return $ \b ->
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

fstFL :: FL (Tuple2FL FL a b :--> a)
fstFL = returnFLF $ \x -> x P.>>= \case
  Tuple2FL a _ -> a

sndFL :: FL (Tuple2FL FL a b :--> b)
sndFL = returnFLF $ \x -> x P.>>= \case
  Tuple2FL _ b -> b

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

data BoolFL (m :: Type -> Type) = FalseFL | TrueFL

type instance Lifted m Bool = BoolFL m

instance HasPrimitiveInfo Bool

instance Narrowable (BoolFL FL) where
  narrow _ _ _ = [(FalseFL, P.Left 0), (TrueFL, P.Left 0)]

instance Convertible Bool where
  to False = FalseFL
  to True = TrueFL
  fromWith _ FalseFL = False
  fromWith _ TrueFL = True

instance Matchable Bool where
  match False FalseFL = P.return ()
  match True  TrueFL  = P.return ()
  match _     _       = P.empty

instance NF Bool (BoolFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible Bool

data UnitFL (m :: Type -> Type) = UnitFL

type instance Lifted m () = UnitFL m

instance HasPrimitiveInfo ()

instance Narrowable (UnitFL FL) where
  narrow _ _ _ = [(UnitFL, P.Left 0)]

instance Convertible () where
  to () = UnitFL
  fromWith _ UnitFL = ()

instance Matchable () where
  match () UnitFL = P.return ()

instance NF () (UnitFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible ()

data OrderingFL (m :: Type -> Type) = LTFL | EQFL | GTFL

type instance Lifted m Ordering = OrderingFL m

instance HasPrimitiveInfo Ordering

instance Narrowable (OrderingFL FL) where
  narrow _ _ _ = [(LTFL , P.Left 0), (EQFL, P.Left 0), (GTFL, P.Left 0)]

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

instance NF Ordering (OrderingFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible Ordering

newtype IntegerFL (m :: Type -> Type) = IntegerFL Integer

type instance Lifted m Integer = IntegerFL m

instance HasPrimitiveInfo Integer where
  primitiveInfo = Primitive

instance Narrowable (IntegerFL FL) where
  narrow = narrowPrimitive

instance Convertible Integer where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Integer where
  match x y = P.guard (x P.== P.coerce y)

instance NF Integer (IntegerFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible Integer

newtype IntFL (m :: Type -> Type) = IntFL P.Int

type instance Lifted m Int = IntFL m

instance HasPrimitiveInfo Int where
  primitiveInfo = Primitive

instance Narrowable (IntFL FL) where
  narrow = narrowPrimitive

instance Convertible Int where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Int where
  match i1 (IntFL i2) = P.guard (i1 P.== i2)

instance NF Int (IntFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible Int

newtype FloatFL (m :: Type -> Type) = FloatFL Float

type instance Lifted m Float = FloatFL m

instance HasPrimitiveInfo Float where
  primitiveInfo = Primitive

instance Narrowable (FloatFL FL) where
  narrow = narrowPrimitive

instance Convertible Float where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Float where
  match x y = P.guard (x P.== P.coerce y)

instance NF Float (FloatFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible Float

newtype DoubleFL (m :: Type -> Type) = DoubleFL Double

type instance Lifted m Double = DoubleFL m

instance HasPrimitiveInfo Double where
  primitiveInfo = Primitive

instance Narrowable (DoubleFL FL) where
  narrow = narrowPrimitive

instance Convertible Double where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable Double where
  match x y = P.guard (x P.== P.coerce y)

instance NF Double (DoubleFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

instance Invertible Double

newtype CharFL (m :: Type -> Type) = CharFL P.Char

type instance Lifted m P.Char = CharFL m

instance HasPrimitiveInfo P.Char where
  primitiveInfo = Primitive

instance Narrowable (CharFL FL) where
  narrow = narrowPrimitive

instance Convertible P.Char where
  to = P.coerce
  fromWith _ = P.coerce

instance Matchable P.Char where
  match x y = P.guard (x P.== P.coerce y)

instance NF P.Char (CharFL FL) where
  normalFormWith _ !x = P.return (P.pure (P.coerce x))

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
    apply2FL appendFL (showFL `appFL` x) s

  showFL :: FL (a :--> StringFL FL)
  showFL = returnFLF $ \x -> apply2FL showsFL x (P.return NilFL)

  showListFL :: FL (ListFL FL a :--> ShowSFL FL)
  showListFL = returnFLF $ \ls -> returnFLF $ \s -> apply3FL showsList__ showsFL ls s

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

shows :: P.Show a => a -> P.ShowS
shows = P.showsPrec 0

showsFL :: ShowFL a => FL (a :--> ShowSFL FL)
showsFL = showsPrecFL `appFL` toFL 0

showString :: P.String -> P.ShowS
showString = (P.++)

showStringFL :: FL (StringFL FL :--> ShowSFL FL)
showStringFL = appendFL

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
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance EqFL (IntegerFL FL) where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance EqFL (FloatFL FL) where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance EqFL (DoubleFL FL) where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance EqFL (CharFL FL) where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

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
eqOn2 x y xs ys = apply2FL (&&#) (apply2FL(==#) x y) (apply2FL(==#) xs ys)

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
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)


instance OrdFL (IntegerFL FL) where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

instance OrdFL (FloatFL FL) where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

instance OrdFL (DoubleFL FL) where
  compareFL = liftFL2Convert P.compare
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

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
  (+#) = primitive2 (P.+) (P.+)
  (-#) = primitive2 (P.-) (P.-)
  (*#) = primitive2 (P.*) (P.*)
  negateFL = primitive1 P.negate P.negate
  absFL    = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = liftFL1Convert P.fromInteger

instance NumFL (IntegerFL FL) where
  (+#) = primitive2 (P.+) (P.+)
  (-#) = primitive2 (P.-) (P.-)
  (*#) = primitive2 (P.*) (P.*)
  negateFL = primitive1 P.negate P.negate
  absFL    = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = returnFLF P.id

instance NumFL (FloatFL FL) where
  (+#) = primitive2 (P.+) (P.+)
  (-#) = primitive2 (P.-) (P.-)
  (*#) = primitive2 (P.*) (P.*)
  negateFL = primitive1 P.negate P.negate
  absFL    = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = liftFL1Convert P.fromInteger

instance NumFL (DoubleFL FL) where
  (+#) = primitive2 (P.+) (P.+)
  (-#) = primitive2 (P.-) (P.-)
  (*#) = primitive2 (P.*) (P.*)
  negateFL = primitive1 P.negate P.negate
  absFL    = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
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
  (/#) = primitive2 (P./) (P./)
  fromRationalFL = liftFL1Convert P.fromRational

instance FractionalFL (DoubleFL FL) where
  (/#) = primitive2 (P./) (P./)
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
  quotFL = primitive2 P.quot sQuot
  remFL  = primitive2 P.rem sRem
  divFL  = primitive2 P.div sDiv
  modFL  = primitive2 P.mod sMod
  divModFL  = primitive2Pair P.divMod sDivMod
  quotRemFL = primitive2Pair P.quotRem sQuotRem
  toIntegerFL = liftFL1Convert P.toInteger

instance IntegralFL (IntegerFL FL) where
  quotFL = primitive2 P.quot sQuot
  remFL  = primitive2 P.rem sRem
  divFL  = primitive2 P.div sDiv
  modFL  = primitive2 P.mod sMod
  divModFL  = primitive2Pair P.divMod sDivMod
  quotRemFL = primitive2Pair P.quotRem sQuotRem
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
  (<|>#) = appendFL


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
    ConsFL x xs -> apply2FL appendFL (f `appFL` x) (apply2FL (>>=#) xs f)

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


withFLVal :: ND FLState (FLVal a) -> (FLVal a -> ND FLState b) -> ND FLState b
withFLVal nd f = nd P.>>= \case
  Var i -> S.get P.>>= \FLState {..} -> f (P.maybe (Var i) Val $ findBinding i heap)
  Val a -> f (Val a)

primitive1 :: forall a' a b' b.
              ( a' ~ Lifted FL a, Constrainable a, Narrowable a', HasPrimitiveInfo a
              , b' ~ Lifted FL b, Constrainable b, Narrowable b', HasPrimitiveInfo b)
           => (a -> b) -> (SBV a -> SBV b) -> FL (a' :--> b')
primitive1 f sF = returnFLF $ \x ->
  FL $
    unFL x `withFLVal` \case
      Val a -> unFL $ returnFL' (coerce (f (coerce a)))
      Var i -> do
        j <- freshIdentifierND
        assertConstraintND (varToSBV j .=== sF (varToSBV i)) [j, i]
        -- Consistency not necessary, see comment in primitive2
        P.return (Var j)

primitive2 :: forall a' a b' b c' c.
              ( a' ~ Lifted FL a, Constrainable a, Narrowable a', HasPrimitiveInfo a
              , b' ~ Lifted FL b, Constrainable b, Narrowable b', HasPrimitiveInfo b
              , c' ~ Lifted FL c, Constrainable c, Narrowable c', HasPrimitiveInfo c)
           => (a -> b -> c) -> (SBV a -> SBV b -> SBV c) -> FL (a' :--> b' :--> c')
primitive2 op sOp = returnFLF $ \x -> returnFLF $ \y ->
  FL $
    unFL x `withFLVal` \x' ->
      unFL y `withFLVal` \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ returnFL' $ coerce (coerce a `op` coerce b)
          _                  -> do
            j <- freshIdentifierND
            assertConstraintND (varToSBV j .=== toSBV x' `sOp` toSBV y') (j : varsOf x' y')
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
              varOf _       = []

primitive2Pair :: forall a' a b' b c' c.
              ( a' ~ Lifted FL a, Constrainable a, Narrowable a', HasPrimitiveInfo a, Convertible a
              , b' ~ Lifted FL b, Constrainable b, Narrowable b', HasPrimitiveInfo b, Convertible b
              , c' ~ Lifted FL c, Constrainable c, Narrowable c', HasPrimitiveInfo c, Convertible c)
           => (a -> b -> (c, c)) -> (SBV a -> SBV b -> (SBV c, SBV c)) -> FL (a' :--> b' :--> Tuple2FL FL c' c')
primitive2Pair op sOp = returnFLF $ \x -> returnFLF $ \y ->
  FL $
    unFL x `withFLVal` \x' ->
      unFL y `withFLVal` \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ returnFL' $ to (coerce a `op` coerce b)
          _                  -> do
            j <- freshIdentifierND
            k <- freshIdentifierND
            assertConstraintND ((varToSBV j, varToSBV k) .=== toSBV x' `sOp` toSBV y') (j : varsOf x' y')
            -- Diss: Checking consistency is unnecessary, because "j" is fresh.
            -- However, it is important to enter x and y in the set of constrained vars, because
            -- they might get constrained indirectly via "j". Example:
            -- j <- x + y
            -- j <- 1
            -- matchFL 9 x
            -- matchFL 0 y
            P.return (Val (Tuple2FL (freeFL j) (freeFL k)))
            where
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = []

primitiveOrd2 :: forall a' a b' b.
              ( a' ~ Lifted FL a, Constrainable a, Narrowable a', HasPrimitiveInfo a
              , b' ~ Lifted FL b, Constrainable b, Narrowable b', HasPrimitiveInfo b)
              => (a -> b -> Bool) -> (SBV a -> SBV b -> SBool) -> FL (a' :--> b' :--> BoolFL FL)
primitiveOrd2 op opS = returnFLF $ \x -> returnFLF $ \y ->
  FL $
    unFL x `withFLVal` \x' ->
      unFL y `withFLVal` \y' ->
        unFL $ case (# x', y' #) of
          (# Val a, Val b #) -> toFL (coerce a `op` coerce b)
          _                  -> FL (trueBranch P.<|> falseBranch)
            where
              trueBranch = do
                assertConstraintND (toSBV x' `opS` toSBV y') (varsOf x' y')
                checkConsistencyND -- DISS: optional, iff x and y were unconstrained
                P.return (Val TrueFL)
              falseBranch = do
                assertConstraintND (sNot (toSBV x' `opS` toSBV y')) (varsOf x' y')
                checkConsistencyND -- DISS: optional, iff x and y were unconstrained
                P.return (Val FalseFL)
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = []
