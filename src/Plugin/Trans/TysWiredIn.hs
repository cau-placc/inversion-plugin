{-|
Module      : Plugin.Trans.TysWiredIn
Description : Module to load built-in type constructors
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains the function to load the initial type constructor map that
connects lifted and unlifted versions of a type constructor.
The map is initialized with some of GHC's built-in types.
-}
module Plugin.Trans.TysWiredIn (loadDefaultTyConMap, builtInModule, maxTupleArity) where

import Data.IORef
import Data.Tuple

import GhcPlugins hiding (int)
import TcRnTypes
import TysPrim
import UniqMap
import Finder
import IfaceEnv
import TcRnMonad
import PrelNames
import HscMain


import Plugin.Trans.Type
import Plugin.Trans.Util (panicAny)

-- | Load the mapping between lifted and unlifted
-- for all built-in type constructors.
loadDefaultTyConMap :: TcM (IORef (UniqMap TyCon TyCon,
                                   UniqMap TyCon TyCon,
                                   UniqSet TyCon,
                                   UniqSet TyCon))
loadDefaultTyConMap = do
  -- Get list of original names and load replacements' from the BuiltIn module.
  loaded <- mapM load originalNamesToLoad
  -- Load any other names that are not in 'PrelNames'
  others <- loadAdditional
  -- Create initial TyConMap
  let allLoaded  = others ++ loaded
  let allSwap    = map swap allLoaded
  let (old, new) = unzip allLoaded
  liftIO (newIORef (listToUniqMap allLoaded,
                    listToUniqMap allSwap,
                    mkUniqSet old,
                    mkUniqSet new))

-- | Get the lifted and unlifted TyCons
-- for the given original and replacement name.
load :: (Name, String, String) -> TcM (TyCon, TyCon)
load (n, m, s) = do
  old <- lookupTyCon n
  new <- getTyCon m s
  return (old, new)

loadAdditional :: TcM [(TyCon, TyCon)]
loadAdditional = do
  -- AlternativeClassName in PrelNames is incorrect, so we look it up manually
  hscEnv <- getTopEnv
  Found _ bse <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Base") Nothing
  altA <- lookupTyCon =<< lookupOrig bse ( mkTcOcc "Alternative" )
  newA <- getTyCon builtInModule "AlternativeFL"

  -- String is not in PrelNames, so we do the same.
  altS <- lookupTyCon =<< lookupOrig bse ( mkTcOcc "String" )
  newS <- getTyCon builtInModule "StringFL"

  let altF = funTyCon
  newF <- getFunTycon

  -- And again for ShowS.
  Found _ shw  <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Show") Nothing
  altH <- lookupTyCon =<< lookupOrig shw ( mkTcOcc "ShowS" )
  newH <- getTyCon builtInModule "ShowSFL"

  -- And again for Real.
  Found _ real <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Real") Nothing
  altR <- lookupTyCon =<< lookupOrig real ( mkTcOcc "Real" )
  newR <- getTyCon builtInModule "RealFL"

  return [ (altH, newH), (altR, newR), (altA, newA)
         , (altS, newS), (altF, newF)
         , (intPrimTyCon, intTyCon)]


-- | A list of GHC's built-in type constructor names and the names of
-- their plugin replacement version.
originalNamesToLoad :: [(Name, String, String)]
originalNamesToLoad = names
  where
    names =
      [ (eqClassName         , builtInModule         , "EqFL")
      , (ordClassName        , builtInModule         , "OrdFL")
      , (showClassName       , builtInModule         , "ShowFL")
      , (enumClassName       , builtInModule         , "EnumFL")
      , (numClassName        , builtInModule         , "NumFL")
      , (integralClassName   , builtInModule         , "IntegralFL")
      , (boundedClassName    , builtInModule         , "BoundedFL")
      , (functorClassName    , builtInModule         , "FunctorFL")
      , (applicativeClassName, builtInModule         , "ApplicativeFL")
      , (monadClassName      , builtInModule         , "MonadFL")
      , (monadFailClassName  , builtInModule         , "MonadFailFL")
      , (isStringClassName   , builtInModule         , "IsStringFL")
      , (listTyConName       , builtInModule         , "ListFL")
      , (rationalTyConName   , builtInModule         , "RationalFL")
      , (ratioTyConName      , builtInModule         , "RatioFL")
      , (charTyConName       , builtInPrimitiveModule, "CharFL")
      , (intTyConName        , builtInPrimitiveModule, "IntFL")
      , (boolTyConName       , builtInModule         , "BoolFL")
      , (orderingTyConName   , builtInModule         , "OrderingFL")
      , (tyConName unitTyCon , builtInModule         , "UnitFL")
      , (integerTyConName    , builtInPrimitiveModule, "IntegerFL")
      ]  ++
      map tupleWithArity [2 .. maxTupleArity]

-- | Create the GHC and plugin names for a tuple of given arity.
tupleWithArity :: Int -> (Name, String, String)
tupleWithArity n = (tupleTyConName BoxedTuple n, builtInModule, "Tuple" ++ show n ++ "FL")

-- | Max tuple arity supported by the plugin.
-- If this is increased, the new tuples
-- have to be added to 'Plugin.InversionPlugin.BuiltIn'.
maxTupleArity :: Int
maxTupleArity = 15

-- | Name of the module that contains all built-in plugin definitions
builtInModule :: String
builtInModule = "Plugin.BuiltIn"

-- | Name of the module that contains all built-in plugin definitions
builtInPrimitiveModule :: String
builtInPrimitiveModule = "Plugin.BuiltIn.Primitive"