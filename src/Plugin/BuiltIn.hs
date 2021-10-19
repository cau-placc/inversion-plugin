{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MagicHash              #-}
{-# LANGUAGE NoStarIsType           #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeApplications       #-}
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
import qualified Data.Functor  as P
import qualified GHC.Base      as P
import qualified GHC.Real      as P
import qualified GHC.Int       as P
import qualified GHC.Stack     as P
import qualified Prelude       as P
import           GHC.Types (RuntimeRep)
import           Unsafe.Coerce ( unsafeCoerce )
import           Prelude ( Bool (..), Double, Float, Int, Integer, Ordering (..), ($) )
import           Data.SBV (SymVal, (.===), (./==), (.>=), (.<=), (.>), (.<), SDivisible (..), SBV, SBool, sNot)

import           Plugin.Effect.Monad as M
import           Plugin.Effect.Util  as M

-- * Lifted list type and internal instances

data ListFL a = NilFL | ConsFL (FL a) (FL (ListFL a))

type StringFL = ListFL CharFL

type instance Lifted [] = ListFL

instance HasPrimitiveInfo (ListFL a)

instance (Narrowable a, HasPrimitiveInfo a) => Narrowable (ListFL a) where
  narrow _ j _ = [(NilFL, 0), (ConsFL (freeFL j) (freeFL (j P.+ 1)), 2)]

instance (Convertible a) => Convertible [a] where
  to [] = NilFL
  to (x : xs) = ConsFL (toFL x) (toFL xs)
  from _ NilFL = []
  from h (ConsFL x xs) = fromFL h x : fromFL h xs

instance (Convertible a, Matchable a, HasPrimitiveInfo (Lifted a)) => Matchable [a] where
  match [] NilFL = M.returnFL ()
  match (x : xs) (ConsFL y ys) = matchFL x y `thenFL` matchFL xs ys
  match _ _ = failedFL

instance Groundable a => Groundable (ListFL a) where
  groundFL p =
    p `bindFL` \case
      NilFL -> M.returnFL NilFL
      ConsFL x xs ->
        groundFL x `bindFL` \y ->
          groundFL xs `bindFL` \ys ->
            M.returnFL (ConsFL (M.returnFL y) (M.returnFL ys))

instance Invertible a => Invertible [a]

data Tuple2FL a b = Tuple2FL (FL a) (FL b)

type instance Lifted (,) = Tuple2FL

instance HasPrimitiveInfo (Tuple2FL a b)

instance (Narrowable a, HasPrimitiveInfo a, Narrowable b, HasPrimitiveInfo b) => Narrowable (Tuple2FL a b) where
  narrow _ j _ = [(Tuple2FL (freeFL j) (freeFL (j P.+ 1)), 2)]

instance (Convertible a, Convertible b) => Convertible (a, b) where
  to (x, y) = Tuple2FL (toFL x) (toFL y)
  from h (Tuple2FL x y) = (fromFL h x, fromFL h y)

instance ( Convertible a, Matchable a, HasPrimitiveInfo (Lifted a)
         , Convertible b, Matchable b, HasPrimitiveInfo (Lifted b))
    => Matchable (a, b) where
  match (x1, x2) (Tuple2FL y1 y2) = matchFL x1 y1 `thenFL` matchFL x2 y2

instance (Groundable a, Groundable b) => Groundable (Tuple2FL a b) where
  groundFL p =
    p `bindFL` \case
      Tuple2FL x y ->
        groundFL x `bindFL` \x' ->
          groundFL y `bindFL` \y' ->

            M.returnFL (Tuple2FL (M.returnFL x') (M.returnFL y'))

instance (Invertible a, Invertible b) => Invertible (a, b)

data Tuple3FL a b c = Tuple3FL (FL a) (FL b) (FL c)

type instance Lifted (,,) = Tuple3FL

instance HasPrimitiveInfo (Tuple3FL a b c)

instance ( Narrowable a, HasPrimitiveInfo a
         , Narrowable b, HasPrimitiveInfo b
         , Narrowable c, HasPrimitiveInfo c)
    => Narrowable (Tuple3FL a b c) where
  narrow _ j _ = [(Tuple3FL (freeFL j) (freeFL (j P.+ 1)) (freeFL (j P.+ 2)), 3)]

instance (Convertible a, Convertible b, Convertible c) => Convertible (a, b, c) where
  to (x, y, z) = Tuple3FL (toFL x) (toFL y) (toFL z)
  from h (Tuple3FL x y z) = (fromFL h x, fromFL h y, fromFL h z)

instance ( Convertible a, Matchable a, HasPrimitiveInfo (Lifted a)
         , Convertible b, Matchable b, HasPrimitiveInfo (Lifted b)
         , Convertible c, Matchable c, HasPrimitiveInfo (Lifted c))
    => Matchable (a, b, c) where
  match (x1, x2, x3) (Tuple3FL y1 y2 y3) = matchFL x1 y1 `thenFL` matchFL x2 y2 `thenFL` matchFL x3 y3

instance (Groundable a, Groundable b, Groundable c) => Groundable (Tuple3FL a b c) where
  groundFL p =
    p `bindFL` \case
      Tuple3FL x y z ->
        groundFL x `bindFL` \x' ->
          groundFL y `bindFL` \y' ->
            groundFL z `bindFL` \z' ->
              M.returnFL (Tuple3FL (M.returnFL x') (M.returnFL y') (M.returnFL z'))

instance (Invertible a, Invertible b, Invertible c) => Invertible (a, b, c)

data Tuple4FL a b c d = Tuple4FL (FL a) (FL b) (FL c) (FL d)

type instance Lifted (,,,) = Tuple4FL

instance HasPrimitiveInfo (Tuple4FL a b c d)

instance ( Narrowable a, HasPrimitiveInfo a
         , Narrowable b, HasPrimitiveInfo b
         , Narrowable c, HasPrimitiveInfo c
         , Narrowable d, HasPrimitiveInfo d)
    => Narrowable (Tuple4FL a b c d) where
  narrow _ j _ = [(Tuple4FL (freeFL j) (freeFL (j P.+ 1)) (freeFL (j P.+ 2)) (freeFL (j P.+ 3)), 4)]

instance (Convertible a, Convertible b, Convertible c, Convertible d) => Convertible (a, b, c, d) where
  to (x, y, z, zz) = Tuple4FL (toFL x) (toFL y) (toFL z) (toFL zz)
  from h (Tuple4FL x y z zz) = (fromFL h x, fromFL h y, fromFL h z, fromFL h zz)

instance ( Convertible a, Matchable a, HasPrimitiveInfo (Lifted a)
         , Convertible b, Matchable b, HasPrimitiveInfo (Lifted b)
         , Convertible c, Matchable c, HasPrimitiveInfo (Lifted c)
         , Convertible d, Matchable d, HasPrimitiveInfo (Lifted d))
    => Matchable (a, b, c, d) where
  match (x1, x2, x3, x4) (Tuple4FL y1 y2 y3 y4) = matchFL x1 y1 `thenFL` matchFL x2 y2 `thenFL` matchFL x3 y3`thenFL` matchFL x4 y4

instance (Groundable a, Groundable b, Groundable c, Groundable d) => Groundable (Tuple4FL a b c d) where
  groundFL p =
    p `bindFL` \case
      Tuple4FL x y z zz ->
        groundFL x `bindFL` \x' ->
          groundFL y `bindFL` \y' ->
            groundFL z `bindFL` \z' ->
              groundFL zz `bindFL` \zz' ->
                M.returnFL (Tuple4FL (M.returnFL x') (M.returnFL y') (M.returnFL z') (M.returnFL zz'))

instance (Invertible a, Invertible b, Invertible c, Invertible d) => Invertible (a, b, c, d)

-- | Lifted defintion for Haskell's 'Ratio' type
data RatioFL a = FL a :% FL a

-- | Lifted defintion for Haskell's 'Rational' type
type RationalFL = RatioFL Integer

type instance Lifted P.Ratio = RatioFL

instance HasPrimitiveInfo (RatioFL a)

instance (Narrowable a, HasPrimitiveInfo a) => Narrowable (RatioFL a) where
  narrow _ j _ = [(freeFL j :% freeFL (j P.+ 1), 2)]

instance (Convertible a) => Convertible (P.Ratio a) where
  to (a P.:% b) = toFL a :% toFL b
  from h (a :% b) = fromFL h a P.:% fromFL h b

instance (Convertible a, Matchable a, HasPrimitiveInfo (Lifted a)) => Matchable (P.Ratio a) where
  match (a1 P.:% b1) (a2 :% b2) = matchFL a1 a2 `thenFL` matchFL b1 b2

instance (Groundable a) => Groundable (RatioFL a) where
  groundFL p =
    p `bindFL` \case
      a :% b ->
        groundFL a `bindFL` \a' ->
          groundFL b `bindFL` \b' ->
            M.returnFL (M.returnFL a' :% M.returnFL b')

-- * For plugin purposes only.

failFLStr :: FL (StringFL --> a)
failFLStr = M.returnFL $ Func $ P.const failedFL

failFLStrFL :: FL (StringFL --> a)
failFLStrFL = failFLStr

-- Lifted seq operator to force evaluation. Forces the effect and value.
seq ::
  forall (k :: RuntimeRep) a b.
  (HasPrimitiveInfo a, Narrowable a) =>
  FL (FL a -> FL (FL b -> FL b))
seq = M.returnFL $ \a -> M.returnFL $ \b ->
  a `bindFL` \a' -> P.seq a' b

-- | Lifted coercion function to replace coercion in newtype-derived instances
-- We need to introduce this unused dummy k,
-- because we replace Data.Coerce.coerce (which has this k).
coerce :: forall (k :: RuntimeRep) a b. FL (a --> b)
coerce = returnFLF $ \(FL a) -> FL $ a P.>>= unsafeCoerce

-- | Lifted equality test for strings
eqString :: FL (StringFL --> StringFL --> Bool)
eqString = (==#)

-- | Lifted equality test for characters
eqChar :: FL (CharFL --> CharFL --> Bool)
eqChar = (==#)

(<##) :: FL (IntFL --> IntFL --> IntFL)
(<##) = returnFLF $ \a -> returnFLF $ \b ->
  a `bindFL` \ (P.I64# a') -> b `bindFL` \ (P.I64# b') -> M.returnFL (P.I64# (a' P.<# b'))

(==##) :: FL (IntFL --> IntFL --> IntFL)
(==##) = returnFLF $ \a -> returnFLF $ \b ->
  a `bindFL` \ (P.I64# a') -> b `bindFL` \ (P.I64# b') -> M.returnFL (P.I64# (a' P.==# b'))

-- * Prelude stuff

undefinedFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . P.HasCallStack => FL a
undefinedFL = failedFL

errorFL :: forall (r :: RuntimeRep) . forall (a :: P.Type) . P.HasCallStack => FL (StringFL --> a)
errorFL = failFLStrFL

notFL :: FL (Bool --> Bool)
notFL = M.returnFL $
  Func $ \x ->
    x `bindFL` \case
      True -> M.returnFL False
      False -> M.returnFL True

idFL :: FL (a --> a)
idFL = returnFLF P.id

fstFL :: FL (Tuple2FL a b --> a)
fstFL = returnFLF $ \t -> t `bindFL` \case
  Tuple2FL a _ -> a

sndFL :: FL (Tuple2FL a b --> b)
sndFL = returnFLF $ \t -> t `bindFL` \case
  Tuple2FL _ b -> b

seqFL ::
  forall (k :: RuntimeRep) a b.
  (Narrowable a, HasPrimitiveInfo a) =>
  FL (FL a -> FL (FL b -> FL b))
seqFL = seq

-- | Lifted const function
constFL :: FL (a --> b --> a)
constFL = returnFLF $ \a -> returnFLF $ P.const a

-- | Lifted logical and
(&&#) :: FL (Bool --> Bool --> Bool)
(&&#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
  a1 `bindFL` \case
    False -> M.returnFL False
    True -> a2

-- | Lifted guard function used to desugar monad comprehensions
guardFL :: (AlternativeFL f) => FL (Bool --> f ())
guardFL = returnFLF $ \b ->
  b `bindFL` \case
    True -> pureFL `appFL` M.returnFL ()
    False -> emptyFL

-- | Lifted append function for lists
appendFL :: FL (ListFL a --> ListFL a --> ListFL a)
appendFL = returnFLF $ \xs -> returnFLF $ \ys ->
  xs `bindFL` \case
    NilFL -> ys
    ConsFL a as -> M.returnFL (ConsFL a (appendFL `appFL` as `appFL` ys))

-- | Lifted concatMap function for lists
concatMapFL :: FL ((a --> ListFL b) --> ListFL a --> ListFL b)
concatMapFL = returnFLF $ \f -> returnFLF $ \xs ->
  xs `bindFL` \case
    NilFL -> M.returnFL NilFL
    ConsFL a as -> appendFL `appFL` (f `appFL` a) `appFL` (concatMapFL `appFL` f `appFL` as)

-- | Lifted map function for lists
mapFL :: FL ((a --> b) --> ListFL a --> ListFL b)
mapFL = returnFLF $ \f -> returnFLF $ \xs ->
  xs `bindFL` \case
    NilFL -> M.returnFL NilFL
    ConsFL a as -> M.returnFL (ConsFL (f `appFL` a) (mapFL `appFL` f `appFL` as))

coerceFL :: forall (k :: RuntimeRep) a b. FL (a --> b)
coerceFL = coerce

-- | Lifted equality test for strings
eqStringFL :: FL (StringFL --> StringFL --> Bool)
eqStringFL = eqString

-- | Lifted equality test for strings
eqCharFL :: FL (CharFL --> CharFL --> Bool)
eqCharFL = eqChar

-- |  Lifted composition operator for functions
(.#) :: FL ((b --> c) --> (a --> b) --> a --> c)
(.#) = returnFLF $ \f1 -> returnFLF $ \f2 -> returnFLF $ \a ->
  f1 `appFL` (f2 `appFL` a)

-- | Lifted append function for lists
(++#) :: FL (ListFL a --> ListFL a --> ListFL a)
(++#) = appendFL

iterateFL :: FL ((a --> a) --> a --> ListFL a)
iterateFL = returnFLF (\f -> returnFLF (\x -> M.returnFL (ConsFL x (iterateFL `appFL` f `appFL` (f `appFL` x)))))

takeWhileFL :: FL ((a --> BoolFL) --> ListFL a --> ListFL a)
takeWhileFL = returnFLF (\p -> returnFLF (\xs -> xs `bindFL` \case
  NilFL       -> M.returnFL NilFL
  ConsFL y ys -> (p `appFL` y) `bindFL` \case
    False -> M.returnFL NilFL
    True  -> M.returnFL (ConsFL y (takeWhileFL `appFL` p `appFL` ys))))

-- * Lifted Show type class, instances and functions

-- | Lifted ShowS type
type ShowSFL = StringFL --> StringFL

type instance Lifted P.Show = ShowFL

-- | Lifted Show type class
class ShowFL a where
  {-# MINIMAL showsPrecFL | showFL #-}
  showsPrecFL :: FL (IntFL --> a --> ShowSFL)
  showsPrecFL = returnFLF $ \_ -> returnFLF $ \x -> returnFLF $ \s ->
    appendFL `appFL` (showFL `appFL` x) `appFL` s

  showFL :: FL (a --> StringFL)
  showFL = returnFLF $ \x -> showsFL `appFL` x `appFL` M.returnFL NilFL

  showListFL :: FL (ListFL a --> ShowSFL)
  showListFL = returnFLF $ \ls -> returnFLF $ \s -> showsList__ `appFL` showsFL `appFL` ls `appFL` s

showsList__ :: FL ((a --> ShowSFL) --> ListFL a --> ShowSFL)
showsList__ = returnFLF $ \showx -> returnFLF $ \list -> returnFLF $ \s ->
  list `bindFL` \case
    NilFL -> appendFL `appFL` M.toFL "[]" `appFL` s
    ConsFL x xs ->
      M.returnFL (ConsFL (toFL '[') (showx `appFL` x `appFL` (showl `appFL` showx `appFL` xs `appFL` s)))
  where
    showl = returnFLF $ \showx -> returnFLF $ \list -> returnFLF $ \s ->
      list `bindFL` \case
        NilFL ->
          M.returnFL (ConsFL (toFL ']') s)
        ConsFL y ys ->
          M.returnFL
            ( ConsFL
                (toFL ',')
                (showx `appFL` y `appFL` (showl `appFL` showx `appFL` ys `appFL` s))
            )

showsFL :: ShowFL a => FL (a --> ShowSFL)
showsFL = showsPrecFL `appFL` M.returnFL 0

showStringFL :: FL (StringFL --> ShowSFL)
showStringFL = appendFL

showCommaSpaceFL :: FL ShowSFL
showCommaSpaceFL = showStringFL `appFL` toFL ", "

showSpaceFL :: FL ShowSFL
showSpaceFL = showStringFL `appFL` toFL " "

showParenFL :: FL (Bool --> ShowSFL --> ShowSFL)
showParenFL = returnFLF $ \b -> returnFLF $ \s ->
  b `bindFL` \case
    True ->
      (.#)
        `appFL` (showStringFL `appFL` toFL "(")
        `appFL` ((.#) `appFL` s `appFL` (showStringFL `appFL` toFL ")"))
    False -> s

instance ShowFL BoolFL where
  showFL = returnFLF $ \x -> x `bindFL` \x' -> toFL (P.show x')

instance ShowFL () where
  showFL = returnFLF $ \x -> x `bindFL` \x' -> toFL (P.show x')

instance (ShowFL a) => ShowFL (ListFL a) where
  showFL = returnFLF $ \xs -> showListFL `appFL` xs `appFL` M.returnFL NilFL

instance ShowFL IntFL where
  showFL = returnFLF $ \x -> x `bindFL` \x' -> toFL (P.show x')

instance ShowFL IntegerFL where
  showFL = returnFLF $ \x -> x `bindFL` \x' -> toFL (P.show x')

instance ShowFL FloatFL where
  showFL = returnFLF $ \x -> x `bindFL` \x' -> toFL (P.show x')

instance ShowFL DoubleFL where
  showFL = returnFLF $ \x -> x `bindFL` \x' -> toFL (P.show x')

-- * Lifted Eq type class, instances and functions

type instance Lifted P.Eq = EqFL

-- | Lifted Eq type class
class EqFL a where
  (==#) :: FL (a --> a --> BoolFL)
  (==#) = returnFLF $ \a1 -> returnFLF $ \a2 -> notFL `appFL` ((/=#) `appFL` a1 `appFL` a2)

  (/=#) :: FL (a --> a --> BoolFL)
  (/=#) = returnFLF $ \a1 -> returnFLF $ \a2 -> notFL `appFL` ((==#) `appFL` a1 `appFL` a2)

instance EqFL BoolFL where
  (==#) = liftFL2 (P.==)
  (/=#) = liftFL2 (P./=)

instance EqFL () where
  (==#) = returnFLF $ \_ -> returnFLF $ \_ -> M.returnFL True
  (/=#) = returnFLF $ \_ -> returnFLF $ \_ -> M.returnFL False

instance (EqFL a) => EqFL (ListFL a) where
  (==#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    a1 `bindFL` \case
      NilFL ->
        a2 `bindFL` \case
          NilFL -> M.returnFL True
          ConsFL _ _ -> M.returnFL False
      ConsFL x xs ->
        a2 `bindFL` \case
          NilFL -> M.returnFL False
          ConsFL y ys -> eqOn x y xs ys

instance (EqFL a, EqFL b) => EqFL (Tuple2FL a b) where
  (==#) = returnFLF $ \x1 -> returnFLF $ \x2 ->
    x1 `bindFL` \(Tuple2FL a1 b1) ->
      x2 `bindFL` \(Tuple2FL a2 b2) ->
        eqOn a1 a2 b1 b2

eqOn :: (EqFL a1, EqFL a2) => FL a1 -> FL a1 -> FL a2 -> FL a2 -> FL Bool
eqOn x y xs ys = (&&#) `appFL` ((==#) `appFL` x `appFL` y) `appFL` ((==#) `appFL` xs `appFL` ys)

-- * Lifted Ord type class, instances and functions

type instance Lifted P.Ord = OrdFL

-- | Lifted Ord type class
class EqFL a => OrdFL a where
  {-# MINIMAL compareFL | (<=#) #-}
  compareFL :: FL (a --> a --> OrderingFL)
  compareFL = returnFLF $ \a1 -> returnFLF $ \a2 ->
    (==#) `appFL` a1 `appFL` a2 `bindFL` \b1 ->
      if b1
        then M.returnFL EQ
        else
          (<=#) `appFL` a1 `appFL` a2 `bindFL` \b2 ->
            if b2
              then M.returnFL LT
              else M.returnFL GT

  (<#) :: FL (a --> a --> BoolFL)
  (<#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    compareFL `appFL` a1 `appFL` a2 `bindFL` \case
      LT -> M.returnFL True
      _ -> M.returnFL False

  (<=#) :: FL (a --> a --> BoolFL)
  (<=#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    compareFL `appFL` a1 `appFL` a2 `bindFL` \case
      GT -> M.returnFL False
      _ -> M.returnFL True

  (>#) :: FL (a --> a --> BoolFL)
  (>#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    compareFL `appFL` a1 `appFL` a2 `bindFL` \case
      GT -> M.returnFL True
      _ -> M.returnFL False

  (>=#) :: FL (a --> a --> BoolFL)
  (>=#) = returnFLF $ \a1 -> returnFLF $ \a2 ->
    compareFL `appFL` a1 `appFL` a2 `bindFL` \case
      LT -> M.returnFL False
      _ -> M.returnFL True

  maxFL :: FL (a --> a --> a)
  maxFL = returnFLF $ \a1 -> returnFLF $ \a2 ->
    (>=#) `appFL` a1 `appFL` a2 `bindFL` \case
      True -> a1
      _ -> a2

  minFL :: FL (a --> a --> a)
  minFL = returnFLF $ \a1 -> returnFLF $ \a2 ->
    (<=#) `appFL` a1 `appFL` a2 `bindFL` \case
      True -> a1
      _ -> a2

instance OrdFL BoolFL where
  compareFL = liftFL2 P.compare

instance OrdFL () where
  compareFL = returnFLF $ \_ -> returnFLF $ \_ -> M.returnFL EQ

instance (OrdFL a) => OrdFL (ListFL a) where
  compareFL = returnFLF $ \x -> returnFLF $ \y ->
    x `bindFL` \x' ->
      y `bindFL` \y' -> case (x', y') of
        (NilFL, NilFL) -> M.returnFL EQ
        (NilFL, ConsFL _ _) -> M.returnFL LT
        (ConsFL _ _, NilFL) -> M.returnFL GT
        (ConsFL a as, ConsFL b bs) ->
          compareFL `appFL` a `appFL` b `bindFL` \case
            EQ -> compareFL `appFL` as `appFL` bs
            o -> M.returnFL o

instance (OrdFL a, OrdFL b) => OrdFL (Tuple2FL a b) where
  compareFL = returnFLF $ \x -> returnFLF $ \y ->
    x `bindFL` \x' ->
      y `bindFL` \y' -> case (x', y') of
        (Tuple2FL a1 b1, Tuple2FL a2 b2) ->
          compareFL `appFL` a1 `appFL` a2 `bindFL` \case
            EQ -> compareFL `appFL` b1 `appFL` b2
            o -> M.returnFL o

-- * Lifted Num type class, instances and functions

type instance Lifted P.Num = NumFL

-- | Lifted Num type class
class NumFL a where
  (+#) :: FL (a --> a --> a)
  (-#) :: FL (a --> a --> a)
  (-#) = returnFLF $ \a -> returnFLF $ \b ->
    (+#) `appFL` a `appFL` (negateFL `appFL` b)
  (*#) :: FL (a --> a --> a)
  negateFL :: FL (a --> a)
  negateFL = returnFLF $ \a ->
    (-#) `appFL` (fromIntegerFL `appFL` M.returnFL 1) `appFL` a
  absFL :: FL (a --> a)
  signumFL :: FL (a --> a)
  fromIntegerFL :: FL (IntegerFL --> a)

-- * Lifted Real type class, instances and functions

type instance Lifted P.Real = RealFL

-- | Lifted Real type class
class (NumFL a, OrdFL a) => RealFL a where
  toRationalFL :: FL (a --> RationalFL)

instance RealFL IntFL where
  toRationalFL = returnFLF $ \x -> M.returnFL ((toIntegerFL `appFL` x ) :% M.returnFL 1)

instance RealFL IntegerFL where
  toRationalFL = returnFLF $ \x -> M.returnFL (x :% M.returnFL 1)

-- * Lifted Integral type class, instances and functions

type instance Lifted P.Integral = IntegralFL

class (RealFL a, EnumFL a) => IntegralFL a where
  quotFL :: FL (a --> a --> a)
  remFL  :: FL (a --> a --> a)
  divFL  :: FL (a --> a --> a)
  modFL  :: FL (a --> a --> a)
  quotRemFL :: FL (a --> a --> Tuple2FL a a)
  divModFL  :: FL (a --> a --> Tuple2FL a a)
  toIntegerFL :: FL (a --> IntegerFL)

  quotFL   = returnFLF $ \n -> returnFLF $ \d -> fstFL `appFL` (quotRemFL `appFL` n `appFL` d)
  remFL    = returnFLF $ \n -> returnFLF $ \d -> sndFL `appFL` (quotRemFL `appFL` n `appFL` d)
  divFL    = returnFLF $ \n -> returnFLF $ \d -> fstFL `appFL` (divModFL `appFL` n `appFL` d)
  modFL    = returnFLF $ \n -> returnFLF $ \d -> sndFL `appFL` (divModFL `appFL` n `appFL` d)

  divModFL = returnFLF $ \n -> returnFLF $ \d ->
    let qr = quotRemFL `appFL` n `appFL` d
        q = fstFL `appFL` qr
        r = sndFL `appFL` qr
    in ((==#) `appFL` (signumFL `appFL` r) `appFL` (negateFL `appFL` (signumFL `appFL` d))) `bindFL` \case
          True  -> M.returnFL $ Tuple2FL ((-#) `appFL` q `appFL` (fromIntegerFL `appFL` M.returnFL 1)) ((+#) `appFL` r `appFL` d)
          False -> qr

instance IntegralFL IntFL where
  quotFL = primitive2 P.quot sQuot
  remFL  = primitive2 P.rem sRem
  divFL  = primitive2 P.div sDiv
  modFL  = primitive2 P.mod sMod

  divModFL = returnFLF $ \x -> returnFLF $ \y ->
    M.returnFL (Tuple2FL (divFL `appFL` x `appFL` y) (modFL `appFL` x `appFL` y))

  quotRemFL = returnFLF $ \x -> returnFLF $ \y ->
    M.returnFL (Tuple2FL (quotFL `appFL` x `appFL` y) (remFL `appFL` x `appFL` y))

  toIntegerFL = liftFL1 P.toInteger

instance IntegralFL IntegerFL where
  quotFL = primitive2 P.quot sQuot
  remFL  = primitive2 P.rem sRem
  divFL  = primitive2 P.div sDiv
  modFL  = primitive2 P.mod sMod

  divModFL = returnFLF $ \x -> returnFLF $ \y ->
    M.returnFL (Tuple2FL (divFL `appFL` x `appFL` y) (modFL `appFL` x `appFL` y))

  quotRemFL = returnFLF $ \x -> returnFLF $ \y ->
    M.returnFL (Tuple2FL (quotFL `appFL` x `appFL` y) (remFL `appFL` x `appFL` y))

  toIntegerFL = idFL

-- * Lifted Monad & Co type classes and instances

type instance Lifted P.Functor = FunctorFL

infixl 1 >>=#, >>#

infixl 4 <$#, <*#, *>#, <*>#

-- | Lifted Functor type class
class FunctorFL f where
  fmapFL :: FL ((a --> b) --> f a --> f b)
  (<$#) :: FL (a --> f b --> f a)
  (<$#) = returnFLF $ \a -> returnFLF $ \f ->
    Plugin.BuiltIn.fmapFL `appFL` (constFL `appFL` a) `appFL` f

instance FunctorFL (Tuple2FL a) where
  fmapFL = returnFLF $ \f -> returnFLF $ \t ->
    t `bindFL` \case
      Tuple2FL a b -> M.returnFL (Tuple2FL a (f `appFL` b))

instance FunctorFL ListFL where
  fmapFL = returnFLF $ \f -> returnFLF $ \l ->
    l `bindFL` \case
      NilFL -> M.returnFL NilFL
      ConsFL x xs -> M.returnFL (ConsFL (f `appFL` x) (Plugin.BuiltIn.fmapFL `appFL` f `appFL` xs))

type instance Lifted P.Applicative = ApplicativeFL

-- | Lifted Applicative type class
class FunctorFL f => ApplicativeFL f where
  pureFL :: FL (a --> f a)

  (<*>#) :: FL (f (a --> b) --> f a --> f b)
  (<*>#) = returnFLF $ \f -> returnFLF $ \a ->
    liftA2FL `appFL` idFL `appFL` f `appFL` a

  liftA2FL :: FL ((a --> b --> c) --> f a --> f b --> f c)
  liftA2FL = returnFLF $ \f -> returnFLF $ \a -> returnFLF $ \b ->
    (<*>#) `appFL` (Plugin.BuiltIn.fmapFL `appFL` f `appFL` a) `appFL` b

  (*>#) :: FL (f a --> f b --> f b)
  (*>#) = returnFLF $ \a -> returnFLF $ \b ->
    liftA2FL `appFL` (constFL `appFL` idFL) `appFL` a `appFL` b

  (<*#) :: FL (f a --> f b --> f a)
  (<*#) = returnFLF $ \a -> returnFLF $ \b ->
    liftA2FL `appFL` constFL `appFL` a `appFL` b
  {-# MINIMAL pureFL, ((<*>#) | liftA2FL) #-}

instance ApplicativeFL ListFL where
  pureFL = returnFLF $ \a -> M.returnFL (ConsFL a (M.returnFL NilFL))
  (<*>#) = returnFLF $ \fs -> returnFLF $ \as ->
    concatMapFL
      `appFL` returnFLF (\a -> Plugin.BuiltIn.fmapFL `appFL` returnFLF (`appFL` a) `appFL` fs)
      `appFL` as

-- | Lifted smart constructor for 'Cons'
cons :: FL (a --> ListFL a --> ListFL a)
cons = returnFLF $ \a -> returnFLF $ \as -> M.returnFL (ConsFL a as)

type instance Lifted P.Alternative = AlternativeFL

-- | Lifted Alternative type class
class ApplicativeFL f => AlternativeFL f where
  emptyFL :: FL (f a)
  (<|>#) :: FL (f a --> f a --> f a)
  someFL :: FL (f a --> f (ListFL a))
  someFL = returnFLF $ \v ->
    let many_v = (<|>#) `appFL` some_v `appFL` (pureFL `appFL` M.returnFL NilFL)
        some_v = liftA2FL `appFL` cons `appFL` v `appFL` many_v
     in some_v
  manyFL :: FL (f a --> f (ListFL a))
  manyFL = returnFLF $ \v ->
    let many_v = (<|>#) `appFL` some_v `appFL` (pureFL `appFL` M.returnFL NilFL)
        some_v = liftA2FL `appFL` cons `appFL` v `appFL` many_v
     in many_v

instance AlternativeFL ListFL where
  emptyFL = M.returnFL NilFL
  (<|>#) = appendFL

type instance Lifted P.Monad = MonadFL

-- | Lifted Monad type class
class ApplicativeFL m => MonadFL m where
  (>>=#) :: FL (m a --> (a --> m b) --> m b)
  (>>#) :: FL (m a --> m b --> m b)
  (>>#) = returnFLF $ \a -> returnFLF $ \b ->
    (>>=#) `appFL` a `appFL` returnFLF (P.const b)
  returnFL :: FL (a --> m a)
  returnFL = pureFL
  {-# MINIMAL (>>=#) #-}

instance MonadFL ListFL where
  (>>=#) = returnFLF $ \a -> returnFLF $ \f ->
    a `bindFL` \case
      NilFL -> M.returnFL NilFL
      ConsFL x xs -> appendFL `appFL` (f `appFL` x) `appFL` ((>>=#) `appFL` xs `appFL` f)

type instance Lifted P.MonadFail = MonadFailFL

-- | Lifted MonadFail type class
class MonadFL m => MonadFailFL m where
  failFL :: FL (StringFL --> m a)

instance MonadFailFL ListFL where
  failFL = returnFLF $ \_ -> M.returnFL NilFL

-- * Lifted Enum type class, instances and functions

class EnumFL a where
    succFL           :: FL (a --> a)
    predFL           :: FL (a --> a)
    toEnumFL         :: FL (IntFL --> a)
    fromEnumFL       :: FL (a --> IntFL)
    enumFromFL       :: FL (a --> ListFL a)
    enumFromThenFL   :: FL (a --> a --> ListFL a)
    enumFromToFL     :: FL (a --> a --> ListFL a)
    enumFromThenToFL :: FL (a --> a --> a --> ListFL a)

    succFL = returnFLF (\x -> toEnumFL `appFL` ((+#) `appFL` M.returnFL 1 `appFL` (fromEnumFL `appFL` x)))

    predFL = returnFLF (\x -> toEnumFL `appFL` ((-#) `appFL` (fromEnumFL `appFL` x) `appFL` M.returnFL 1))

    enumFromFL = returnFLF (\x -> mapFL `appFL` toEnumFL `appFL` (enumFromFL `appFL` (fromEnumFL `appFL` x)))

    enumFromThenFL = returnFLF (\x -> returnFLF (\y -> mapFL `appFL` toEnumFL `appFL`
      (enumFromThenFL `appFL` (fromEnumFL `appFL` x) `appFL` (fromEnumFL `appFL` y))))

    enumFromToFL = returnFLF (\x -> returnFLF (\y -> mapFL `appFL` toEnumFL `appFL`
      (enumFromToFL `appFL` (fromEnumFL `appFL` x) `appFL` (fromEnumFL `appFL` y))))

    enumFromThenToFL = returnFLF (\x -> returnFLF (\y -> returnFLF (\z -> mapFL `appFL` toEnumFL `appFL`
      (enumFromThenToFL `appFL` (fromEnumFL `appFL` x) `appFL` (fromEnumFL `appFL` y) `appFL` (fromEnumFL `appFL` z)))))

-- * Lifted Bounded type class, instances and functions

type instance Lifted P.Bounded = BoundedFL

-- | Lifted Bounded type class
class BoundedFL a where
  minBoundFL :: FL a
  maxBoundFL :: FL a

instance BoundedFL () where
  minBoundFL = M.returnFL ()
  maxBoundFL = M.returnFL ()

instance BoundedFL BoolFL where
  minBoundFL = M.returnFL False
  maxBoundFL = M.returnFL True

class IsStringFL a where
  fromStringFL :: FL (StringFL --> a)

instance (a ~ CharFL) => IsStringFL (ListFL a) where
  fromStringFL = returnFLF P.id

instance EqFL CharFL where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance OrdFL CharFL where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

withFLVal :: ND (FLVal a) -> (FLVal a -> ND b) -> ND b
withFLVal nd f = nd P.>>= \case
  Var i -> S.lift S.get P.>>= \(_, h, _) -> f (P.maybe (Var i) Val $ findBinding i h)
  Val a -> f (Val a)

primitive1 :: ( SymVal a, Narrowable a, HasPrimitiveInfo a
              , SymVal b, Narrowable b, HasPrimitiveInfo b)
           => (a -> b) -> (SBV a -> SBV b) -> FL (a --> b)
primitive1 f sF = returnFLF $ \x ->
  FL $
    unFL x `withFLVal` \case
      Val a -> unFL $ returnFL' (f a)
      x'    -> do
        j <- freshIdentifierND
        assertConstraintND (toSBV (Var j) .=== sF (toSBV x')) (j : varOf x')
        -- Consistency not necessary, see comment in primitive2
        P.return (Var j)
        where
          varOf (Var i) = [i]
          varOf _       = []

primitive2 :: ( SymVal a, Narrowable a, HasPrimitiveInfo a
              , SymVal b, Narrowable b, HasPrimitiveInfo b
              , SymVal c, Narrowable c, HasPrimitiveInfo c)
           => (a -> b -> c) -> (SBV a -> SBV b -> SBV c) -> FL (a --> b --> c)
primitive2 op sOp = returnFLF $ \x -> returnFLF $ \y ->
  FL $
    unFL x `withFLVal` \x' ->
      unFL y `withFLVal` \y' ->
        case (# x', y' #) of
          (# Val a, Val b #) -> unFL $ returnFL' (a `op` b)
          _                  -> do
            j <- freshIdentifierND
            assertConstraintND (toSBV (Var j) .=== toSBV x' `sOp` toSBV y') (j : varsOf x' y')
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

primitiveOrd2 :: (SymVal a, SymVal b) => (a -> b -> Bool) -> (SBV a -> SBV b -> SBool) -> FL (a --> b --> BoolFL)
primitiveOrd2 op opS = returnFLF $ \x -> returnFLF $ \y ->
  FL $
    unFL x `withFLVal` \x' ->
      unFL y `withFLVal` \y' ->
        unFL $ case (# x', y' #) of
          (# Val a, Val b #) -> M.returnFL (a `op` b)
          _                  -> FL $ (trueBranch P.$> Val True) P.<|> (falseBranch P.$> Val False)
            where
              trueBranch = do
                assertConstraintND (toSBV x' `opS` toSBV y') (varsOf x' y')
                checkConsistencyND -- DISS: optional, iff x and y were unconstrained
              falseBranch = do
                assertConstraintND (sNot (toSBV x' `opS` toSBV y')) (varsOf x' y')
                checkConsistencyND -- DISS: optional, iff x and y were unconstrained
              varsOf x'' y'' = varOf x'' P.++ varOf y''
              varOf (Var i) = [i]
              varOf _       = []

instance EqFL IntFL where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance OrdFL IntFL where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

instance NumFL IntFL where
  (+#) = primitive2 (P.+) (P.+)
  (*#) = primitive2 (P.*) (P.*)
  (-#) = primitive2 (P.-) (P.-)
  negateFL = primitive1 P.negate P.negate
  absFL = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = liftFL1 P.fromInteger

instance EnumFL IntFL where
  toEnumFL   = idFL
  fromEnumFL = idFL
  succFL = returnFLF (\x -> (+#) `appFL` x `appFL` M.returnFL 1)
  predFL = returnFLF (\x -> (-#) `appFL` x `appFL` M.returnFL 1)
  enumFromFL = returnFLF (\x -> M.returnFL (ConsFL x (enumFromFL `appFL` (succFL `appFL` x))))
  enumFromToFL = returnFLF (\x -> returnFLF (\y -> ((>#) `appFL` x `appFL` y) `bindFL` \case
    False -> M.returnFL (ConsFL x (enumFromToFL `appFL` (succFL `appFL` x) `appFL` y))
    True  -> M.returnFL NilFL))
  enumFromThenFL = returnFLF (\x -> returnFLF (\y ->
    iterateFL `appFL` ((+#) `appFL` ((-#) `appFL` y `appFL` x)) `appFL` x))
  enumFromThenToFL = returnFLF (\x -> returnFLF (\y -> returnFLF (\z ->
    let
      test = returnFLF (\x' -> ((>=#) `appFL` y `appFL` x) `bindFL` \case
        False -> (>=#) `appFL` x' `appFL` z
        True  -> (<=#) `appFL` x' `appFL` z)
    in takeWhileFL `appFL` test `appFL` (enumFromThenFL `appFL` x `appFL` y))))

instance EqFL IntegerFL where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance OrdFL IntegerFL where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

instance NumFL IntegerFL where
  (+#) = primitive2 (P.+) (P.+)
  (*#) = primitive2 (P.*) (P.*)
  (-#) = primitive2 (P.-) (P.-)
  negateFL = primitive1 P.negate P.negate
  absFL = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = idFL

instance EnumFL IntegerFL where
  toEnumFL   = toIntegerFL
  fromEnumFL = fromIntegerFL
  succFL = returnFLF (\x -> (+#) `appFL` x `appFL` M.returnFL 1)
  predFL = returnFLF (\x -> (-#) `appFL` x `appFL` M.returnFL 1)
  enumFromFL = returnFLF (\x -> M.returnFL (ConsFL x (enumFromFL `appFL` (succFL `appFL` x))))
  enumFromToFL = returnFLF (\x -> returnFLF (\y -> ((>#) `appFL` x `appFL` y) `bindFL` \case
    False -> M.returnFL (ConsFL x (enumFromToFL `appFL` (succFL `appFL` x) `appFL` y))
    True  -> M.returnFL NilFL))
  enumFromThenFL = returnFLF (\x -> returnFLF (\y ->
    iterateFL `appFL` ((+#) `appFL` ((-#) `appFL` y `appFL` x)) `appFL` x))
  enumFromThenToFL = returnFLF (\x -> returnFLF (\y -> returnFLF (\z ->
    let
      test = returnFLF (\x' -> ((>=#) `appFL` y `appFL` x) `bindFL` \case
        False -> (>=#) `appFL` x' `appFL` z
        True  -> (<=#) `appFL` x' `appFL` z)
    in takeWhileFL `appFL` test `appFL` (enumFromThenFL `appFL` x `appFL` y))))

instance EqFL FloatFL where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance OrdFL FloatFL where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

instance NumFL FloatFL where
  (+#) = primitive2 (P.+) (P.+)
  (*#) = primitive2 (P.*) (P.*)
  (-#) = primitive2 (P.-) (P.-)
  negateFL = primitive1 P.negate P.negate
  absFL = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = liftFL1 P.fromInteger

instance EqFL DoubleFL where
  (==#) = primitiveOrd2 (P.==) (.===)
  (/=#) = primitiveOrd2 (P./=) (./==)

instance OrdFL DoubleFL where
  (>=#) = primitiveOrd2 (P.>=) (.>=)
  (<=#) = primitiveOrd2 (P.<=) (.<=)
  (>#) = primitiveOrd2 (P.>) (.>)
  (<#) = primitiveOrd2 (P.<) (.<)

instance NumFL DoubleFL where
  (+#) = primitive2 (P.+) (P.+)
  (*#) = primitive2 (P.*) (P.*)
  (-#) = primitive2 (P.-) (P.-)
  negateFL = primitive1 P.negate P.negate
  absFL = primitive1 P.abs P.abs
  signumFL = primitive1 P.signum P.signum
  fromIntegerFL = liftFL1 P.fromInteger

-----------------------------------------------------------------------------------

type BoolFL = Bool

type instance Lifted Bool = BoolFL

instance HasPrimitiveInfo BoolFL

instance Narrowable BoolFL

instance Convertible Bool

instance Matchable Bool

instance Groundable BoolFL

instance Invertible Bool

type instance Lifted () = ()

instance HasPrimitiveInfo ()

instance Narrowable ()

instance Convertible ()

instance Matchable ()

instance Groundable ()

instance Invertible ()

type OrderingFL = Ordering

type instance Lifted Ordering = OrderingFL

instance HasPrimitiveInfo OrderingFL

instance Narrowable OrderingFL

instance Convertible Ordering

instance Matchable Ordering

instance Groundable OrderingFL

instance Invertible Ordering

type IntegerFL = Integer

type instance Lifted Integer = IntegerFL

instance HasPrimitiveInfo IntegerFL where
  primitiveInfo = Primitive

instance Narrowable IntegerFL where
  narrow = narrowPrimitive

instance Convertible Integer

instance Matchable Integer

instance Groundable IntegerFL

instance Invertible Integer

type IntFL = P.Int64

type instance Lifted Int = IntFL

instance HasPrimitiveInfo IntFL where
  primitiveInfo = Primitive

instance Narrowable IntFL where
  narrow = narrowPrimitive

instance Convertible Int where
  to = P.fromIntegral
  from _ = P.fromIntegral

instance Matchable Int where
  match i64 iFL = if iFL P.== P.fromIntegral i64
    then M.returnFL ()
    else failedFL

instance Groundable IntFL

instance Invertible Int

type FloatFL = Float

type instance Lifted Float = FloatFL

instance HasPrimitiveInfo FloatFL where
  primitiveInfo = Primitive

instance Narrowable FloatFL where
  narrow = narrowPrimitive

instance Convertible Float

instance Matchable Float

instance Groundable FloatFL

instance Invertible Float

type DoubleFL = Double

type instance Lifted Double = DoubleFL

instance HasPrimitiveInfo DoubleFL where
  primitiveInfo = Primitive

instance Narrowable DoubleFL where
  narrow = narrowPrimitive

instance Convertible Double

instance Matchable Double

instance Groundable DoubleFL

instance Invertible Double

type CharFL = P.Char

type instance Lifted P.Char = CharFL

instance HasPrimitiveInfo CharFL where
  primitiveInfo = Primitive

instance Narrowable CharFL where
  narrow = narrowPrimitive

instance Convertible P.Char

instance Matchable P.Char

instance Groundable CharFL

instance Invertible P.Char
