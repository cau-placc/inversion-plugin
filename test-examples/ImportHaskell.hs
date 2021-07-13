{-# OPTIONS_GHC -fplugin Plugin.InversionPlugin #-}
module ImportHaskell where

import ExportHaskell

-- Compilation of this module is expected to fail
-- due to import of a plain Haskell module (see ExportHaskell.hs).
