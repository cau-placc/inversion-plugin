{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use camelCase" #-}

{-|
Module      : Plugin.Trans.FunWiredIn
Description : Functions to look up the replacement of wired-in functions
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module provides a look up for wired-in functions.
There are two reasons to replace a function:
  1. It is used in a derived instance.
     Derived instances always use the functions from the default Prelude.
  2. It is a default implementation of a built-in type class that requires
     Sharing. Adding a Shareable constraints to built-in class
     functions is not supported, so we replace any used default implementation
     with something different during lifting.
-}
module Plugin.Trans.FunWiredIn (lookupWiredInFunc) where

import Data.List

import GHC.Builtin.Names
import GHC.Iface.Env
import GHC.Plugins
import GHC.Tc.Types
import GHC.Unit.Finder (FindResult(..), findImportedModule)
import GHC.Tc.Utils.Monad
import GHC.Types.TyThing

import Plugin.Trans.TysWiredIn
import Plugin.Trans.Util
import Plugin.Trans.Var

-- | look up the replacement for a wired-in function or return the original
-- if no replacement is known or required.
lookupWiredInFunc :: Var -> Type -> TcM Var
lookupWiredInFunc v ty = do
  wired <- mapM lookupRdrBase wiredIn
  case find (== varName v) wired of
    Nothing -> return (setVarType v ty)
    Just n -> do
      hscEnv <- getTopEnv
      Found _ mdl <- liftIO $
        findImportedModule hscEnv (mkModuleName builtInModule) Nothing
      lookupId =<< lookupOrig mdl (addNameSuffix $ occName n)

-- | Look up the Name for a given RdrName
-- where the original name is already known.
lookupRdrBase :: RdrName -> TcM Name
lookupRdrBase n = case isOrig_maybe n of
  Just (m, o) -> lookupOrig m o
  Nothing     -> panicAnyUnsafe "Non-origininal name in lookup" n

-- A list of all wired-in functions. Their replacement always has the same name
-- and is defined in 'Plugin.BuiltIn'.
wiredIn :: [RdrName]
wiredIn =
  [ mkOrig gHC_PRIM    (mkVarOcc "coerce")
  , mkOrig mONAD       (mkVarOcc "guard")
  , mkOrig gHC_BASE    (mkVarOcc "map")
  , mkOrig gHC_BASE    (mkVarOcc "not")
  , mkOrig gHC_BASE    (mkVarOcc "eqString")
  , mkOrig gHC_SHOW    (mkVarOcc "showString")
  , mkOrig gHC_SHOW    (mkVarOcc "showCommaSpace")
  , mkOrig gHC_SHOW    (mkVarOcc "showSpace")
  , mkOrig gHC_SHOW    (mkVarOcc "showParen")
  , mkOrig gHC_BASE    (mkVarOcc ".")
  , mkOrig gHC_BASE    (mkVarOcc "eqString")
  , mkOrig gHC_CLASSES (mkVarOcc "eqChar")
  , mkOrig gHC_ERR     (mkVarOcc "error")
  , mkOrig gHC_ERR     (mkVarOcc "undefined")
  , mkOrig gHC_PRIM    (mkVarOcc "<#")
  , mkOrig gHC_PRIM    (mkVarOcc "==#")
  , mkOrig gHC_BASE    (mkVarOcc "++")
  , mkOrig gHC_LIST    (mkVarOcc "filter")
  , mkOrig gHC_BASE    (mkVarOcc "$")
  , mkOrig dATA_MAYBE  (mkVarOcc "fromJust")
  ]

dATA_MAYBE :: Module
dATA_MAYBE = mkBaseModule (fsLit "Data.Either")
