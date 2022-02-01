{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTSyntax                #-}
{-# LANGUAGE InstanceSigs              #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilyDependencies    #-}

{-# OPTIONS_GHC -Wno-orphans              #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Unused LANGUAGE pragma" #-}

module Plugin.Effect.SolverLibrary.What4 () where

#ifdef USE_WHAT4

import Data.Bits
import Data.BitVector.Sized
import Data.Coerce
import Data.IORef
import Data.Parameterized
import Data.Parameterized.Nonce
import Data.Text
import Data.Typeable

import GHC.Float
import GHC.Magic

import qualified Language.Haskell.TH as TH

import LibBF

import System.IO.Unsafe

import                Plugin.BuiltIn.Primitive
import {-# SOURCE #-} Plugin.Effect.Monad

import What4.Config
import What4.Expr
import What4.Expr.Builder
import What4.Interface
import What4.ProblemFeatures
import What4.Protocol.Online
import What4.Protocol.SMTLib2
import What4.Solver
import What4.Utils.StringLiteral

#ifndef USE_CVC4
type What4Solver = Z3
#else
type What4Solver = CVC4
#endif

what4SolverOptions :: [ConfigDesc]
what4SolverOptions = case show (typeRep (Proxy @What4Solver)) of
  "CVC4" -> cvc4Options
  "Z3"   -> z3Options
  _      -> error "unsupported solver"

what4SolverFeatures :: ProblemFeatures
what4SolverFeatures = case show (typeRep (Proxy @What4Solver)) of
  "CVC4" -> cvc4Features
  "Z3"   -> z3Features
  _      -> error "unsupported solver"

instance SolverLibrary where
  type Constraint = What4Constraint

  checkConsistency cs = unsafePerformIO $ do
    Some (ng :: NonceGenerator IO x) <- newIONonceGenerator
    sym <- newExprBuilder FloatIEEERepr Proxy ng
    ref <- newIORef emptyHeap
    ref2 <- newIORef []
    extendConfig what4SolverOptions (getConfiguration sym)
    solver <- startSolverProcess what4SolverFeatures Nothing sym :: IO (SolverProcess x (Writer What4Solver))
    let conn = solverConn solver
    mapM (toPred sym ref ref2) cs >>= mapM_ (assume conn)
    readIORef ref2 >>= mapM_ (assume conn)
    runCheckSat (Session conn (solverResponse solver)) $ \res -> do
      _ <- shutdownSolverProcess solver
      case res of
        Sat _ -> return True
        _     -> return False

  type Constrainable a = What4Constrainable a

  getModels :: forall a. Constrainable a => ID -> [Constraint] -> [a]
  getModels i cs = unsafePerformIO $ do
    Some (ng :: NonceGenerator IO x) <- newIONonceGenerator
    sym <- newExprBuilder FloatIEEERepr Proxy ng
    ref <- newIORef emptyHeap
    ref2 <- newIORef []
    extendConfig what4SolverOptions (getConfiguration sym)
    solver <- startSolverProcess what4SolverFeatures Nothing sym :: IO (SolverProcess x (Writer What4Solver))
    let conn = solverConn solver
    mapM (toPred sym ref ref2) cs >>= mapM_ (assume conn)
    v <- varToSym @_ @a sym ref ref2 i --TODO: important, because otherwise length == 1 constraints for strings wouldn't be created
    readIORef ref2 >>= mapM_ (assume conn)
    let getModelsRecursive () =
          runCheckSat (Session conn (solverResponse solver)) $ \case
            Sat (ge, _) -> do
              x <- groundEval ge v
              let c = InternalNeqConstraint i x (Proxy @a)
              toPred sym ref ref2 c >>= assume conn
              return $ fromGroundValue x : unsafePerformIO (getModelsRecursive (noinline const () c))
            _           -> shutdownSolverProcess solver >> return []
    getModelsRecursive (noinline const () v)

  eqConstraint  = EqConstraint
  notConstraint = NotConstraint

  intPlusConstraint   = Just IntPlusConstraint
  intMinusConstraint  = Just IntMinusConstraint
  intMulConstraint    = Just IntMulConstraint
  intNegateConstraint = Just IntNegateConstraint
  intAbsConstraint    = Just IntAbsConstraint
  intSignumConstraint = Just IntSignumConstraint

  integerPlusConstraint   = Just IntegerPlusConstraint
  integerMinusConstraint  = Just IntegerMinusConstraint
  integerMulConstraint    = Just IntegerMulConstraint
  integerNegateConstraint = Just IntegerNegateConstraint
  integerAbsConstraint    = Just IntegerAbsConstraint
  integerSignumConstraint = Just IntegerSignumConstraint

  floatPlusConstraint   = Just FloatPlusConstraint
  floatMinusConstraint  = Just FloatMinusConstraint
  floatMulConstraint    = Just FloatMulConstraint
  floatNegateConstraint = Just FloatNegateConstraint
  floatAbsConstraint    = Just FloatAbsConstraint
  floatSignumConstraint = Just FloatSignumConstraint

  doublePlusConstraint   = Just DoublePlusConstraint
  doubleMinusConstraint  = Just DoubleMinusConstraint
  doubleMulConstraint    = Just DoubleMulConstraint
  doubleNegateConstraint = Just DoubleNegateConstraint
  doubleAbsConstraint    = Just DoubleAbsConstraint
  doubleSignumConstraint = Just DoubleSignumConstraint

  intLtConstraint  = Just IntLtConstraint
  intLeqConstraint = Just IntLeqConstraint
  intGtConstraint  = Just IntGtConstraint
  intGeqConstraint = Just IntGeqConstraint
  intMaxConstraint = Just IntMaxConstraint
  intMinConstraint = Just IntMinConstraint

  integerLtConstraint  = Just IntegerLtConstraint
  integerLeqConstraint = Just IntegerLeqConstraint
  integerGtConstraint  = Just IntegerGtConstraint
  integerGeqConstraint = Just IntegerGeqConstraint
  integerMaxConstraint = Just IntegerMaxConstraint
  integerMinConstraint = Just IntegerMinConstraint

  floatLtConstraint  = Just FloatLtConstraint
  floatLeqConstraint = Just FloatLeqConstraint
  floatGtConstraint  = Just FloatGtConstraint
  floatGeqConstraint = Just FloatGeqConstraint
  floatMaxConstraint = Just FloatMaxConstraint
  floatMinConstraint = Just FloatMinConstraint

  doubleLtConstraint  = Just DoubleLtConstraint
  doubleLeqConstraint = Just DoubleLeqConstraint
  doubleGtConstraint  = Just DoubleGtConstraint
  doubleGeqConstraint = Just DoubleGeqConstraint
  doubleMaxConstraint = Just DoubleMaxConstraint
  doubleMinConstraint = Just DoubleMinConstraint

  charLtConstraint  = Nothing
  charLeqConstraint = Nothing
  charGtConstraint  = Nothing
  charGeqConstraint = Nothing
  charMaxConstraint = Nothing
  charMinConstraint = Nothing

data What4Constraint where
  EqConstraint :: forall a. Constrainable a => FLVal a -> FLVal a -> What4Constraint
  NotConstraint :: Constraint -> What4Constraint
  InternalNeqConstraint :: forall a. Constrainable a => ID -> GroundValue (What4BaseType a) -> Proxy a -> What4Constraint

  IntPlusConstraint, IntMinusConstraint, IntMulConstraint :: FLVal (IntFL FL) -> FLVal (IntFL FL) -> FLVal (IntFL FL) -> What4Constraint
  IntNegateConstraint, IntAbsConstraint, IntSignumConstraint:: FLVal (IntFL FL) -> FLVal (IntFL FL) -> What4Constraint

  IntegerPlusConstraint, IntegerMinusConstraint, IntegerMulConstraint :: FLVal (IntegerFL FL) -> FLVal (IntegerFL FL) -> FLVal (IntegerFL FL) -> What4Constraint
  IntegerNegateConstraint, IntegerAbsConstraint, IntegerSignumConstraint:: FLVal (IntegerFL FL) -> FLVal (IntegerFL FL) -> What4Constraint

  FloatPlusConstraint, FloatMinusConstraint, FloatMulConstraint :: FLVal (FloatFL FL) -> FLVal (FloatFL FL) -> FLVal (FloatFL FL) -> What4Constraint
  FloatNegateConstraint, FloatAbsConstraint, FloatSignumConstraint:: FLVal (FloatFL FL) -> FLVal (FloatFL FL) -> What4Constraint

  DoublePlusConstraint, DoubleMinusConstraint, DoubleMulConstraint :: FLVal (DoubleFL FL) -> FLVal (DoubleFL FL) -> FLVal (DoubleFL FL) -> What4Constraint
  DoubleNegateConstraint, DoubleAbsConstraint, DoubleSignumConstraint:: FLVal (DoubleFL FL) -> FLVal (DoubleFL FL) -> What4Constraint

  IntLtConstraint, IntLeqConstraint, IntGtConstraint, IntGeqConstraint :: FLVal (IntFL FL) -> FLVal (IntFL FL) -> What4Constraint
  IntMaxConstraint, IntMinConstraint :: FLVal (IntFL FL) -> FLVal (IntFL FL) -> FLVal (IntFL FL) -> What4Constraint

  IntegerLtConstraint, IntegerLeqConstraint, IntegerGtConstraint, IntegerGeqConstraint :: FLVal (IntegerFL FL) -> FLVal (IntegerFL FL) -> What4Constraint
  IntegerMaxConstraint, IntegerMinConstraint :: FLVal (IntegerFL FL) -> FLVal (IntegerFL FL) -> FLVal (IntegerFL FL) -> What4Constraint

  FloatLtConstraint, FloatLeqConstraint, FloatGtConstraint, FloatGeqConstraint :: FLVal (FloatFL FL) -> FLVal (FloatFL FL) -> What4Constraint
  FloatMaxConstraint, FloatMinConstraint :: FLVal (FloatFL FL) -> FLVal (FloatFL FL) -> FLVal (FloatFL FL) -> What4Constraint

  DoubleLtConstraint, DoubleLeqConstraint, DoubleGtConstraint, DoubleGeqConstraint :: FLVal (DoubleFL FL) -> FLVal (DoubleFL FL) -> What4Constraint
  DoubleMaxConstraint, DoubleMinConstraint :: FLVal (DoubleFL FL) -> FLVal (DoubleFL FL) -> FLVal (DoubleFL FL) -> What4Constraint

toPred :: IsSymExprBuilder sym => sym -> IORef Heap -> IORef [Pred sym] -> Constraint -> IO (Pred sym)
toPred sym ref ref2 (EqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  isEq' sym symX symY
toPred sym ref ref2 (NotConstraint c) = do
  toPred sym ref ref2 c >>= notPred sym
toPred sym ref ref2 (InternalNeqConstraint i v (_ :: Proxy a)) = do
  symI <- varToSym @_ @a sym ref ref2 i
  symV <- lit sym $ fromGroundValue v
  isEq' sym symI symV >>= notPred sym
toPred sym ref ref2 (IntPlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symRes <- snd <$> addSignedOF sym symX symY
  bvEq sym symZ symRes
toPred sym ref ref2 (IntMinusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symRes <- snd <$> subSignedOF sym symX symY
  bvEq sym symZ symRes
toPred sym ref ref2 (IntMulConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symRes <- snd <$> mulSignedOF sym symX symY
  bvEq sym symZ symRes
toPred sym ref ref2 (IntNegateConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  bvNeg sym symX >>= bvEq sym symY
toPred sym ref ref2 (IntAbsConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symIsNeg <- bvIsNeg sym symX
  symRes <- bvNeg sym symX >>= flip (bvIte sym symIsNeg) symX
  bvEq sym symY symRes --TODO: check
toPred sym ref ref2 (IntSignumConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  sym0 <- lit sym (coerce @Int 0)
  sym1 <- lit sym (coerce @Int 1)
  symNeg1 <- lit sym (coerce @Int (-1))
  symIsNeg <- bvIsNeg sym symX
  symIs0 <- bvEq sym symX sym0
  symRes <- bvIte sym symIsNeg symNeg1 sym1 >>= bvIte sym symIs0 sym0
  bvEq sym symY symRes --TODO: check
toPred sym ref ref2 (IntegerPlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  intAdd sym symX symY >>= isEq' sym symZ
toPred sym ref ref2 (IntegerMinusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  intSub sym symX symY >>= isEq' sym symZ
toPred sym ref ref2 (IntegerMulConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  intMul sym symX symY >>= isEq' sym symZ
toPred sym ref ref2 (IntegerNegateConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  intNeg sym symX >>= isEq' sym symY
toPred sym ref ref2 (IntegerAbsConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  intAbs sym symX >>= isEq' sym symY
toPred sym ref ref2 (IntegerSignumConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  sym0 <- lit sym (coerce @Integer 0)
  sym1 <- lit sym (coerce @Integer 1)
  symNeg1 <- lit sym (coerce @Integer (-1))
  symIsNeg <- intLt sym symX sym0
  symIs0 <- isEq' sym symX sym0
  symRes <- intIte sym symIsNeg symNeg1 sym1 >>= intIte sym symIs0 sym0
  isEq' sym symY symRes --TODO: check
toPred sym ref ref2 (FloatPlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatAdd sym RTZ symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (FloatMinusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatSub sym RTZ symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (FloatMulConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatMul sym RTZ symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (FloatNegateConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatNeg sym symX >>= floatFpEq sym symY
toPred sym ref ref2 (FloatAbsConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatAbs sym symX >>= floatFpEq sym symY
toPred sym ref ref2 (FloatSignumConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  sym0 <- floatPZero sym floatFloatingPointPrecisionRepr
  symNeg0 <- floatNZero sym floatFloatingPointPrecisionRepr
  sym1 <- lit sym (coerce @Float 1.0)
  symNeg1 <- lit sym (coerce @Float (-1.0))
  symNaN <- floatNaN sym floatFloatingPointPrecisionRepr
  symIsNaN <- floatIsNaN sym symX
  symIsNeg <- floatIsNeg sym symX
  symIs0 <- floatIsZero sym symX
  sym0OrNeg0Res <- floatIte sym symIsNeg symNeg0 sym0
  sym1OrNeg1Res <- floatIte sym symIsNeg symNeg1 sym1
  symRes <- floatIte sym symIs0 sym0OrNeg0Res sym1OrNeg1Res >>= floatIte sym symIsNaN symNaN
  floatFpEq sym symY symRes --TODO: check
toPred sym ref ref2 (DoublePlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatAdd sym RTZ symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (DoubleMinusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatSub sym RTZ symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (DoubleMulConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatMul sym RTZ symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (DoubleNegateConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatNeg sym symX >>= floatFpEq sym symY
toPred sym ref ref2 (DoubleAbsConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatAbs sym symX >>= floatFpEq sym symY
toPred sym ref ref2 (DoubleSignumConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  sym0 <- floatPZero sym doubleFloatingPointPrecisionRepr
  symNeg0 <- floatNZero sym doubleFloatingPointPrecisionRepr
  sym1 <- lit sym (coerce @Double 1.0)
  symNeg1 <- lit sym (coerce @Double (-1.0))
  symNaN <- floatNaN sym doubleFloatingPointPrecisionRepr
  symIsNaN <- floatIsNaN sym symX
  symIsNeg <- floatIsNeg sym symX
  symIs0 <- floatIsZero sym symX
  sym0OrNeg0Res <- floatIte sym symIsNeg symNeg0 sym0
  sym1OrNeg1Res <- floatIte sym symIsNeg symNeg1 sym1
  symRes <- floatIte sym symIs0 sym0OrNeg0Res sym1OrNeg1Res >>= floatIte sym symIsNaN symNaN
  floatFpEq sym symY symRes --TODO: check
toPred sym ref ref2 (IntLtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  bvSlt sym symX symY
toPred sym ref ref2 (IntLeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  bvSle sym symX symY
toPred sym ref ref2 (IntGtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  bvSgt sym symX symY
toPred sym ref ref2 (IntGeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  bvSge sym symX symY
toPred sym ref ref2 (IntMaxConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symIsGt <- bvSgt sym symX symY
  bvIte sym symIsGt symX symY >>= isEq' sym symZ
toPred sym ref ref2 (IntMinConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symIsLt <- bvSlt sym symX symY
  bvIte sym symIsLt symX symY >>= isEq' sym symZ
toPred sym ref ref2 (IntegerLtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  intLt sym symX symY
toPred sym ref ref2 (IntegerLeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  intLe sym symX symY
toPred sym ref ref2 (IntegerGtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  flip (intLt sym) symX symY -- TODO: Why is there no intGt?
toPred sym ref ref2 (IntegerGeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  flip (intLe sym) symX symY -- TODO: Why is there no intGeq?
toPred sym ref ref2 (IntegerMaxConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symIsGt <- flip (intLt sym) symX symY
  intIte sym symIsGt symX symY >>= isEq' sym symZ
toPred sym ref ref2 (IntegerMinConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symIsLt <- intLt sym symX symY
  intIte sym symIsLt symX symY >>= isEq' sym symZ
toPred sym ref ref2 (FloatLtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatLt sym symX symY
toPred sym ref ref2 (FloatLeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatLe sym symX symY
toPred sym ref ref2 (FloatGtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatGt sym symX symY
toPred sym ref ref2 (FloatGeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatGe sym symX symY
toPred sym ref ref2 (FloatMaxConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatMax sym symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (FloatMinConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatMin sym symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (DoubleLtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatLt sym symX symY
toPred sym ref ref2 (DoubleLeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatLe sym symX symY
toPred sym ref ref2 (DoubleGtConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatGt sym symX symY
toPred sym ref ref2 (DoubleGeqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  floatGe sym symX symY
toPred sym ref ref2 (DoubleMaxConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatMax sym symX symY >>= floatFpEq sym symZ
toPred sym ref ref2 (DoubleMinConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatMin sym symX symY >>= floatFpEq sym symZ

-- TODO: comment
isEq' :: IsExprBuilder sym => sym -> SymExpr sym tp -> SymExpr sym tp -> IO (Pred sym)
isEq' sym x y = case exprType x of
  BaseBoolRepr      -> eqPred sym x y
  BaseBVRepr {}     -> bvEq sym x y
  BaseIntegerRepr   -> intEq sym x y
  BaseRealRepr      -> realEq sym x y
  BaseFloatRepr {}  -> floatFpEq sym x y
  BaseComplexRepr   -> cplxEq sym x y
  BaseStringRepr {} -> stringEq sym x y
  BaseStructRepr {} -> structEq sym x y
  BaseArrayRepr {}  -> arrayEq sym x y

toSym :: (IsSymExprBuilder sym, Constrainable a) => sym -> IORef Heap -> IORef [Pred sym] -> FLVal a -> IO (SymExpr sym (What4BaseType a))
toSym sym ref ref2 (Var i) = varToSym sym ref ref2 i
toSym sym _   _    (Val x) = lit sym x

varToSym :: forall sym a. (IsSymExprBuilder sym, Constrainable a) => sym -> IORef Heap -> IORef [Pred sym] -> ID -> IO (SymExpr sym (What4BaseType a))
varToSym sym ref ref2 i = do
  h <- readIORef ref
  case findBinding i h of
    Nothing -> do
      e <- freshConstant sym (safeSymbol (show i)) what4BaseTypeRepr
      case exprType e of
        BaseStringRepr _ -> do
          symL <- stringLength sym e
          p <- intLit sym 1 >>= isEq' sym symL
          modifyIORef ref2 (p :)
        _                -> return ()
      writeIORef ref (insertBinding i e h)
      return e
    Just e  -> return e

class Typeable a => What4Constrainable a where
  type family What4BaseType a = (b :: BaseType) | b -> a
  what4BaseTypeRepr :: BaseTypeRepr (What4BaseType a)
  lit :: IsSymExprBuilder sym => sym -> a -> IO (SymExpr sym (What4BaseType a))
  fromGroundValue :: GroundValue (What4BaseType a) -> a

instance What4Constrainable (IntFL FL) where
  type instance What4BaseType (IntFL FL) = BaseBVType $(return $ TH.LitT $ TH.NumTyLit $ toInteger $ finiteBitSize @Int 0)
  what4BaseTypeRepr = BaseBVRepr (knownNat @($(return $ TH.LitT $ TH.NumTyLit $ toInteger $ finiteBitSize @Int 0)))
  lit sym = bvLit sym (knownNat @($(return $ TH.LitT $ TH.NumTyLit $ toInteger $ finiteBitSize @Int 0))) . mkBV (knownNat @($(return $ TH.LitT $ TH.NumTyLit $ toInteger $ finiteBitSize @Int 0))) . toInteger . coerce @(IntFL FL) @Int
  fromGroundValue = coerce @Int @(IntFL FL) . fromInteger . asSigned (knownNat @($(return $ TH.LitT $ TH.NumTyLit $ toInteger $ finiteBitSize @Int 0)))

instance What4Constrainable (IntegerFL FL) where
  type instance What4BaseType (IntegerFL FL) = BaseIntegerType
  what4BaseTypeRepr = BaseIntegerRepr
  lit sym = intLit sym . coerce
  fromGroundValue = coerce

doubleFloatingPointPrecisionRepr :: FloatPrecisionRepr Prec64
doubleFloatingPointPrecisionRepr = FloatingPointPrecisionRepr (knownNat @11) (knownNat @53)

instance What4Constrainable (DoubleFL FL) where
  type instance What4BaseType (DoubleFL FL) = BaseFloatType Prec64
  what4BaseTypeRepr = BaseFloatRepr doubleFloatingPointPrecisionRepr
  lit sym = floatLit sym doubleFloatingPointPrecisionRepr . bfFromDouble . coerce
  fromGroundValue = coerce . fst . bfToDouble ToZero

floatFloatingPointPrecisionRepr :: FloatPrecisionRepr Prec32
floatFloatingPointPrecisionRepr = FloatingPointPrecisionRepr (knownNat @8) (knownNat @24)

instance What4Constrainable (FloatFL FL) where
  type instance What4BaseType (FloatFL FL) = BaseFloatType Prec32
  what4BaseTypeRepr = BaseFloatRepr floatFloatingPointPrecisionRepr
  lit sym = floatLit sym floatFloatingPointPrecisionRepr . bfFromDouble . float2Double . coerce
  fromGroundValue = coerce . double2Float . fst . bfToDouble ToZero

instance What4Constrainable (CharFL FL) where
  type instance What4BaseType (CharFL FL) = BaseStringType Unicode
  what4BaseTypeRepr = BaseStringRepr UnicodeRepr
  lit sym = stringLit sym . UnicodeLiteral . pack . return . coerce
  fromGroundValue = coerce . Data.Text.head . fromUnicodeLit

#endif
