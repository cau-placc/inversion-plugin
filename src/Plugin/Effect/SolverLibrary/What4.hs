{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
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
import Data.Data
import Data.IORef
import Data.Parameterized
import Data.Parameterized.Nonce
import Data.Text                (pack, unpack)

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

  eqConstraint = EqConstraint
  notConstraint = NotConstraint

  intPlusConstraint = Just IntPlusConstraint
  integerPlusConstraint = Just IntegerPlusConstraint
  floatPlusConstraint = Just FloatPlusConstraint
  doublePlusConstraint = Just DoublePlusConstraint

data What4Constraint
  = forall a. Constrainable a => EqConstraint (FLVal a) (FLVal a)
  | NotConstraint Constraint
  | forall a. Constrainable a => InternalNeqConstraint ID (GroundValue (What4BaseType a)) (Proxy a)
  | IntPlusConstraint (FLVal (IntFL FL)) (FLVal (IntFL FL)) (FLVal (IntFL FL))
  | IntegerPlusConstraint (FLVal (IntegerFL FL)) (FLVal (IntegerFL FL)) (FLVal (IntegerFL FL))
  | FloatPlusConstraint (FLVal (FloatFL FL)) (FLVal (FloatFL FL)) (FLVal (FloatFL FL))
  | DoublePlusConstraint (FLVal (DoubleFL FL)) (FLVal (DoubleFL FL)) (FLVal (DoubleFL FL))

toPred :: IsSymExprBuilder sym => sym -> IORef Heap -> IORef [Pred sym] -> Constraint -> IO (Pred sym)
toPred sym ref ref2 (EqConstraint x y) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  isEq sym symX symY
toPred sym ref ref2 (NotConstraint c) = do
  toPred sym ref ref2 c >>= notPred sym
toPred sym ref ref2 (InternalNeqConstraint i v (_ :: Proxy a)) = do
  symI <- varToSym @_ @a sym ref ref2 i
  symV <- lit sym $ fromGroundValue v
  isEq sym symI symV >>= notPred sym
toPred sym ref ref2 (IntPlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  symRes <- snd <$> addSignedOF sym symX symY
  isEq sym symZ symRes
toPred sym ref ref2 (IntegerPlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  intAdd sym symX symY >>= isEq sym symZ
toPred sym ref ref2 (FloatPlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatAdd sym RTZ symX symY >>= isEq sym symZ
toPred sym ref ref2 (DoublePlusConstraint x y z) = do
  symX <- toSym sym ref ref2 x
  symY <- toSym sym ref ref2 y
  symZ <- toSym sym ref ref2 z
  floatAdd sym RTZ symX symY >>= isEq sym symZ

toSym :: (IsSymExprBuilder sym, Constrainable a) => sym -> IORef Heap -> IORef [Pred sym] -> FLVal a -> IO (SymExpr sym (What4BaseType a))
toSym sym ref ref2 (Var i) = varToSym sym ref ref2 i
toSym sym _   _    (Val x) = lit sym x

varToSym :: forall sym a. (IsSymExprBuilder sym, Constrainable a) => sym -> IORef Heap -> IORef [Pred sym] -> ID -> IO (SymExpr sym (What4BaseType a))
varToSym sym ref ref2 i = do
  h <- readIORef ref
  case findBinding i h of
    Nothing -> do
      e <- freshConstant sym (safeSymbol (show i)) what4BaseTypeRepr
      case eqT @a @(CharFL FL) of
        Just Refl -> do
          symL <- stringLength sym e
          p <- intLit sym 1 >>= isEq sym symL
          modifyIORef ref2 (p :)
        _         -> return ()
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

doubleFloatingPointRepr :: FloatPrecisionRepr Prec64
doubleFloatingPointRepr = FloatingPointPrecisionRepr (knownNat @11) (knownNat @53)

instance What4Constrainable (DoubleFL FL) where
  type instance What4BaseType (DoubleFL FL) = BaseFloatType Prec64
  what4BaseTypeRepr = BaseFloatRepr doubleFloatingPointRepr
  lit sym = floatLit sym doubleFloatingPointRepr . bfFromDouble . coerce
  fromGroundValue = coerce . fst . bfToDouble ToZero

floatFloatingPointRepr :: FloatPrecisionRepr Prec32
floatFloatingPointRepr = FloatingPointPrecisionRepr (knownNat @8) (knownNat @24)

instance What4Constrainable (FloatFL FL) where
  type instance What4BaseType (FloatFL FL) = BaseFloatType Prec32
  what4BaseTypeRepr = BaseFloatRepr floatFloatingPointRepr
  lit sym = floatLit sym floatFloatingPointRepr . bfFromDouble . float2Double . coerce
  fromGroundValue = coerce . double2Float . fst . bfToDouble ToZero

instance What4Constrainable (CharFL FL) where
  type instance What4BaseType (CharFL FL) = BaseStringType Unicode
  what4BaseTypeRepr = BaseStringRepr UnicodeRepr
  lit sym = stringLit sym . UnicodeLiteral . pack . return . coerce
  fromGroundValue = coerce . head . unpack . fromUnicodeLit

#endif
