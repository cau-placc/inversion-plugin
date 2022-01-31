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
#ifndef USE_CVC4
runSBVSolver = runSMTWith z3
#else
runSBVSolver = runSMTWith cvc4
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
        initialC = v .=== v
        getModelsRecursive cs' = unsafePerformIO $ runSBVSolver $ do
          query $ checkSatAssuming cs' >>= \case
            Sat -> do
              x <- getValue @(SBVType a) v
              let c = v ./== literal x
              return $ coerce x : getModelsRecursive (c : cs')
            _   -> return []
    in getModelsRecursive (initialC : cs)

  eqConstraint = liftSBVOrd2 (.===)
  notConstraint = sNot
  neqConstraint = liftSBVOrd2 (./==)

  intPlusConstraint = Just $ liftSBV2 (+)
  intMinusConstraint = Just $ liftSBV2 (-)
  intMulConstraint = Just $ liftSBV2 (*)
  integerPlusConstraint = Just $ liftSBV2 (+)
  integerMinusConstraint = Just $ liftSBV2 (-)
  integerMulConstraint = Just $ liftSBV2 (*)
  floatPlusConstraint = Just $ liftSBV2 (+)
  floatMinusConstraint = Just $ liftSBV2 (-)
  floatMulConstraint = Just $ liftSBV2 (*)
  doublePlusConstraint = Just $ liftSBV2 (+)
  doubleMinusConstraint = Just $ liftSBV2 (-)
  doubleMulConstraint = Just $ liftSBV2 (*)

  intLtConstraint = Just $ liftSBVOrd2 (.<)
  integerLtConstraint = Just $ liftSBVOrd2 (.<)
  floatLtConstraint = Just $ liftSBVOrd2 (.<)
  doubleLtConstraint = Just $ liftSBVOrd2 (.<)
  charLtConstraint = Just $ liftSBVOrd2 (.<)

  intLeqConstraint = Just $ liftSBVOrd2 (.<=)
  integerLeqConstraint = Just $ liftSBVOrd2 (.<=)
  floatLeqConstraint = Just $ liftSBVOrd2 (.<=)
  doubleLeqConstraint = Just $ liftSBVOrd2 (.<=)
  charLeqConstraint = Just $ liftSBVOrd2 (.<=)

  intGtConstraint = Just $ liftSBVOrd2 (.>)
  integerGtConstraint = Just $ liftSBVOrd2 (.>)
  floatGtConstraint = Just $ liftSBVOrd2 (.>)
  doubleGtConstraint = Just $ liftSBVOrd2 (.>)
  charGtConstraint = Just $ liftSBVOrd2 (.>)

  intGeqConstraint = Just $ liftSBVOrd2 (.>=)
  integerGeqConstraint = Just $ liftSBVOrd2 (.>=)
  floatGeqConstraint = Just $ liftSBVOrd2 (.>=)
  doubleGeqConstraint = Just $ liftSBVOrd2 (.>=)
  charGeqConstraint = Just $ liftSBVOrd2 (.>=)

  --TODO: max, min

type family SBVType a = b | b -> a where
  SBVType (IntFL FL) = Int
  SBVType (IntegerFL FL) = Integer
  SBVType (FloatFL FL) = Float
  SBVType (DoubleFL FL) = Double
  SBVType (CharFL FL) = Char

liftSBV2 :: (Constrainable a, Constrainable b, Constrainable c) => (SBV (SBVType a) -> SBV (SBVType b) -> SBV (SBVType c)) -> FLVal a -> FLVal b -> FLVal c -> SBool
liftSBV2 sOp x y z = toSBV x `sOp` toSBV y .=== toSBV z

liftSBVOrd2 :: Constrainable a => (SBV (SBVType a) -> SBV (SBVType a) -> SBool) -> FLVal a -> FLVal a -> SBool
liftSBVOrd2 sOp x y = toSBV x `sOp` toSBV y

toSBV :: Constrainable a => FLVal a -> SBV (SBVType a)
toSBV (Var i) = varToSBV i
toSBV (Val x) = literal (coerce x)

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
