{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE TypeFamilies          #-}

module Plugin.Effect.Monad where

import qualified Data.Kind
import           Data.IntMap (IntMap)

import Plugin.Lifted

--------------------------------------------------------------------------------

type ID = Int

--------------------------------------------------------------------------------

data Untyped

insertBinding :: ID -> FL a -> IntMap Untyped -> IntMap Untyped

lookupBinding :: ID -> IntMap Untyped -> Maybe (FL a)

--------------------------------------------------------------------------------

class SolverLibrary where
  type Constraint

  checkConsistency :: [Constraint] -> Bool

  type Constrainable a :: Data.Kind.Constraint

  getModels :: Constrainable a => ID -> [Constraint] -> [a]

  eqConstraint :: Constrainable a => FLVal a -> FLVal a -> Constraint
  notConstraint :: Constraint -> Constraint
  neqConstraint :: Constrainable a => FLVal a -> FLVal a -> Constraint
  neqConstraint x y = notConstraint (eqConstraint x y)

  intPlusConstraint, intMinusConstraint, intMulConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)
  intNegateConstraint, intAbsConstraint, intSignumConstraint:: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)

  intQuotConstraint, intRemConstraint, intDivConstraint, intModConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)

  integerPlusConstraint, integerMinusConstraint, integerMulConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)
  integerNegateConstraint, integerAbsConstraint, integerSignumConstraint:: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)

  integerQuotConstraint, integerRemConstraint, integerDivConstraint, integerModConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)

  floatPlusConstraint, floatMinusConstraint, floatMulConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)
  floatNegateConstraint, floatAbsConstraint, floatSignumConstraint:: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)

  floatDivConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)

  doublePlusConstraint, doubleMinusConstraint, doubleMulConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)
  doubleNegateConstraint, doubleAbsConstraint, doubleSignumConstraint:: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  doubleDivConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  intLtConstraint, intLeqConstraint, intGtConstraint, intGeqConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)
  intMaxConstraint, intMinConstraint :: Maybe (FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> FLVal (Lifted FL Int) -> Constraint)

  integerLtConstraint, integerLeqConstraint, integerGtConstraint, integerGeqConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)
  integerMaxConstraint, integerMinConstraint :: Maybe (FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> FLVal (Lifted FL Integer) -> Constraint)

  floatLtConstraint, floatLeqConstraint, floatGtConstraint, floatGeqConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)
  floatMaxConstraint, floatMinConstraint :: Maybe (FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> FLVal (Lifted FL Float) -> Constraint)

  doubleLtConstraint, doubleLeqConstraint, doubleGtConstraint, doubleGeqConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)
  doubleMaxConstraint, doubleMinConstraint :: Maybe (FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> FLVal (Lifted FL Double) -> Constraint)

  charLtConstraint, charLeqConstraint, charGtConstraint, charGeqConstraint :: Maybe (FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> Constraint)
  charMaxConstraint, charMinConstraint :: Maybe (FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> FLVal (Lifted FL Char) -> Constraint)

--------------------------------------------------------------------------------

class HasPrimitiveInfo (a :: Data.Kind.Type)

--------------------------------------------------------------------------------

data FLVal (a :: Data.Kind.Type) where
  Var        :: HasPrimitiveInfo a => ID -> FLVal a
  Val        :: a -> FLVal a
  HaskellVal :: To b => b -> FLVal (Lifted FL b)

--------------------------------------------------------------------------------

type role FL nominal

data FL (a :: Data.Kind.Type)

--------------------------------------------------------------------------------

class To (a :: Data.Kind.Type)

to :: To a => a -> Lifted FL a

--TODO: hs-boot file aufräumen
