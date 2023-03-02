module SBVTest where

import Data.SBV
import Data.SBV.Control

t :: IO ()
t = runSMTWith cvc5 {transcript=Just "bad.smt2", verbose=True} $ do
        --let x = sym "x" :: SBV Char
        x <- sChar "x"
        let y = sym "y" :: SBV Char

        query $ do cs <- checkSatAssuming [x .=== y]
                   case cs of
                     Sat -> do
                               xv <- getValue x
                               io $ print xv
                     _   -> error $ "solver said: " ++ show cs
