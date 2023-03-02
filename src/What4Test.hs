{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module What4Test where

import Data.Data
import Data.Parameterized
import Data.Parameterized.Nonce
import Data.Text

import System.IO.Unsafe

import What4.Config
import What4.Expr
import What4.Interface
import What4.Protocol.Online
import What4.Protocol.SMTLib2
import What4.Solver
import What4.Utils.StringLiteral

unsafeGetChars :: [Char]
unsafeGetChars = unsafePerformIO $ do
    Some (ng :: NonceGenerator IO x) <- newIONonceGenerator
    sym <- newExprBuilder FloatIEEERepr Proxy ng
    extendConfig cvc4Options (getConfiguration sym)
    solver <- startSolverProcess cvc4Features Nothing sym :: IO (SolverProcess x (Writer CVC4))
    let conn = solverConn solver
    -- Create string var and constrain its length to 1
    x <- freshConstant sym (safeSymbol "x") (BaseStringRepr UnicodeRepr)
    l <- stringLength sym x
    intLit sym 1 >>= isEq sym l >>= assume conn
    -- Recursively generate characters
    let getModelsRecursive =
          runCheckSat (Session conn (solverResponse solver)) $ \case
            Sat (ge, _) -> do
              v <- groundEval ge x
              -- Exclude value
              stringLit sym v >>= isEq sym x >>= notPred sym >>= assume conn
              return $ (Data.Text.head . fromUnicodeLit) v : unsafePerformIO getModelsRecursive
            _           -> shutdownSolverProcess solver >> return []
    getModelsRecursive

getChars :: Int -> IO [Char]
getChars n = do
    Some (ng :: NonceGenerator IO x) <- newIONonceGenerator
    sym <- newExprBuilder FloatIEEERepr Proxy ng
    extendConfig z3Options (getConfiguration sym)
    solver <- startSolverProcess z3Features Nothing sym :: IO (SolverProcess x (Writer Z3))
    let conn = solverConn solver
    -- Create string var and constrain its length to 1
    x <- freshConstant sym (safeSymbol "x") (BaseStringRepr UnicodeRepr)
    l <- stringLength sym x
    intLit sym 1 >>= isEq sym l >>= assume conn
    -- Recursively generate characters
    let getModelsRecursive 0  = return []
        getModelsRecursive n' =
          runCheckSat (Session conn (solverResponse solver)) $ \case
            Sat (ge, _) -> do
              v <- groundEval ge x
              -- Exclude value
              stringLit sym v >>= isEq sym x >>= notPred sym >>= assume conn
              rest <- getModelsRecursive (n' - 1)
              return $ (Data.Text.head . fromUnicodeLit) v : rest
            _           -> shutdownSolverProcess solver >> return []
    getModelsRecursive n

getProblematicChar :: IO Char
getProblematicChar = do
  Some (ng :: NonceGenerator IO x) <- newIONonceGenerator
  sym <- newExprBuilder FloatIEEERepr Proxy ng
  extendConfig z3Options (getConfiguration sym)
  solver <- startSolverProcess z3Features Nothing sym :: IO (SolverProcess x (Writer Z3))
  let conn = solverConn solver
  x <- freshConstant sym (safeSymbol "x") (BaseStringRepr UnicodeRepr)
  l <- stringLength sym x
  intLit sym 1 >>= isEq sym l >>= assume conn
  stringLit sym (UnicodeLiteral (pack "\\")) >>= isEq sym x >>= assume conn
  runCheckSat (Session conn (solverResponse solver)) $ \case
    Sat (ge, _) -> do
      v <- groundEval ge x
      _ <- shutdownSolverProcess solver
      return $ Data.Text.head $ fromUnicodeLit v
    _           -> error "unsatisfiable"
