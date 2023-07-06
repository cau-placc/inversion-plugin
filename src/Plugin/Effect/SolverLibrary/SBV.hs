{-# LANGUAGE CPP                    #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -Wno-orphans              #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Unused LANGUAGE pragma" #-}

module Plugin.Effect.SolverLibrary.SBV () where

#ifndef USE_WHAT4

import Data.Coerce
import Data.SBV
import Data.SBV.Control
import Data.SBV.Internals hiding (SBVType)

import                Plugin.BuiltIn.Primitive
import {-# SOURCE #-} Plugin.Effect.Monad

import System.IO.Unsafe

runSBVSolver :: Symbolic a -> IO a
#ifdef USE_CVC
runSBVSolver = runSMTWith cvc5
#elif defined(USE_Z3)
runSBVSolver = runSMTWith z3
#else
#error No solver specified
#endif

instance SolverLibrary where
  type Constraint = SBool

  checkConsistency cs = unsafePerformIO $ runSBVSolver $
    query $ checkSatAssuming cs >>= \case
      Sat -> return True
      _   -> return False

  type Constrainable a = (SymVal (SBVType a), Coercible a (SBVType a))

  getModels :: forall a. Constrainable a => ID -> [Constraint] -> [a]
  getModels i cs =
    let v = varToSBV @(SBVType a) i
        dummyV = sym @(SBV (SBVType a)) "dummy" -- TODO: Comment that this is needed in order to get character models
        initialC = v .=== dummyV
        getModelsRecursive cs' = unsafePerformIO $ runSBVSolver $ do
          query $ checkSatAssuming cs' >>= \case
            Sat -> do
              x <- getValue @(SBVType a) v
              let c = v ./== literal x
              return $ coerce x : getModelsRecursive (c : cs')
            _   -> return []
    in getModelsRecursive (initialC : cs)

  eqConstraint  = liftSBVOrd2 (.==)
  notConstraint = sNot
  neqConstraint = liftSBVOrd2 (./=)

  intPlusConstraint   = Just $ liftSBV2 (+)
  intMinusConstraint  = Just $ liftSBV2 (-)
  intMulConstraint    = Just $ liftSBV2 (*)
  intNegateConstraint = Just $ liftSBV1 negate
  intAbsConstraint    = Just $ liftSBV1 abs
  intSignumConstraint = Just $ liftSBV1 signum

  intQuotConstraint = Just $ liftSBV2 sQuot
  intRemConstraint  = Just $ liftSBV2 sRem
  intDivConstraint  = Just $ liftSBV2 sDiv
  intModConstraint  = Just $ liftSBV2 sMod

  integerPlusConstraint   = Just $ liftSBV2 (+)
  integerMinusConstraint  = Just $ liftSBV2 (-)
  integerMulConstraint    = Just $ liftSBV2 (*)
  integerNegateConstraint = Just $ liftSBV1 negate
  integerAbsConstraint    = Just $ liftSBV1 abs
  integerSignumConstraint = Just $ liftSBV1 signum

  integerQuotConstraint = Just $ liftSBV2 sQuot
  integerRemConstraint  = Just $ liftSBV2 sRem
  integerDivConstraint  = Just $ liftSBV2 sDiv
  integerModConstraint  = Just $ liftSBV2 sMod

  floatPlusConstraint   = Just $ liftSBV2 (+)
  floatMinusConstraint  = Just $ liftSBV2 (-)
  floatMulConstraint    = Just $ liftSBV2 (*)
  floatNegateConstraint = Just $ liftSBV1 negate
  floatAbsConstraint    = Just $ liftSBV1 abs
  floatSignumConstraint = Just $ liftSBV1 signum

  floatDivConstraint = Just $ liftSBV2 (/)

  doublePlusConstraint   = Just $ liftSBV2 (+)
  doubleMinusConstraint  = Just $ liftSBV2 (-)
  doubleMulConstraint    = Just $ liftSBV2 (*)
  doubleNegateConstraint = Just $ liftSBV1 negate
  doubleAbsConstraint    = Just $ liftSBV1 abs
  doubleSignumConstraint = Just $ liftSBV1 signum

  doubleDivConstraint = Just $ liftSBV2 (/)

  intLtConstraint  = Just $ liftSBVOrd2 (.<)
  intLeqConstraint = Just $ liftSBVOrd2 (.<=)
  intGtConstraint  = Just $ liftSBVOrd2 (.>)
  intGeqConstraint = Just $ liftSBVOrd2 (.>=)
  intMaxConstraint = Just $ liftSBV2 smax
  intMinConstraint = Just $ liftSBV2 smin

  integerLtConstraint  = Just $ liftSBVOrd2 (.<)
  integerLeqConstraint = Just $ liftSBVOrd2 (.<=)
  integerGtConstraint  = Just $ liftSBVOrd2 (.>)
  integerGeqConstraint = Just $ liftSBVOrd2 (.>=)
  integerMaxConstraint = Just $ liftSBV2 smax
  integerMinConstraint = Just $ liftSBV2 smin

  floatLtConstraint  = Just $ liftSBVOrd2 (.<)
  floatLeqConstraint = Just $ liftSBVOrd2 (.<=)
  floatGtConstraint  = Just $ liftSBVOrd2 (.>)
  floatGeqConstraint = Just $ liftSBVOrd2 (.>=)
  floatMaxConstraint = Just $ liftSBV2 smax
  floatMinConstraint = Just $ liftSBV2 smin

  doubleLtConstraint  = Just $ liftSBVOrd2 (.<)
  doubleLeqConstraint = Just $ liftSBVOrd2 (.<=)
  doubleGtConstraint  = Just $ liftSBVOrd2 (.>)
  doubleGeqConstraint = Just $ liftSBVOrd2 (.>=)
  doubleMaxConstraint = Just $ liftSBV2 smax
  doubleMinConstraint = Just $ liftSBV2 smin

  charLtConstraint  = Just $ liftSBVOrd2 (.<)
  charLeqConstraint = Just $ liftSBVOrd2 (.<=)
  charGtConstraint  = Just $ liftSBVOrd2 (.>)
  charGeqConstraint = Just $ liftSBVOrd2 (.>=)
  charMaxConstraint = Just $ liftSBV2 smax
  charMinConstraint = Just $ liftSBV2 smin

type family SBVType a = b | b -> a where
  SBVType (IntFL FL) = Int
  SBVType (IntegerFL FL) = Integer
  SBVType (FloatFL FL) = Float
  SBVType (DoubleFL FL) = Double
  SBVType (CharFL FL) = Char

liftSBV1 :: (Constrainable a, Constrainable b) => (SBV (SBVType a) -> SBV (SBVType b)) -> FLVal a -> FLVal b -> SBool
liftSBV1 sF x y = sF (toSBV x) .=== toSBV y

liftSBV2 :: (Constrainable a, Constrainable b, Constrainable c) => (SBV (SBVType a) -> SBV (SBVType b) -> SBV (SBVType c)) -> FLVal a -> FLVal b -> FLVal c -> SBool
liftSBV2 sOp x y z = toSBV x `sOp` toSBV y .=== toSBV z

liftSBVOrd2 :: Constrainable a => (SBV (SBVType a) -> SBV (SBVType a) -> SBool) -> FLVal a -> FLVal a -> SBool
liftSBVOrd2 sOp x y = toSBV x `sOp` toSBV y

toSBV :: Constrainable a => FLVal a -> SBV (SBVType a)
toSBV (Var i)        = varToSBV i
toSBV (Val x)        = literal (coerce x)
toSBV (HaskellVal x) = literal (coerce (to x))

varToSBV :: SymVal a => ID -> SBV a
varToSBV i = sym $ "x" ++ (if i < 0 then "n" else "") ++ show (abs i)

instance SymVal Int where
  mkSymVal = genMkSymVar (KBounded True (finiteBitSize @Int 0))
  literal  = genLiteral (KBounded True (finiteBitSize @Int 0))
  fromCV   = genFromCV

instance HasKind Int where
  kindOf _ = KBounded True (finiteBitSize @Int 0)

instance SDivisible (SBV Int) where
  sQuotRem = liftQRem
  sDivMod  = liftDMod

#endif
