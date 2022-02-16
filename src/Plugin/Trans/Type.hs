{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase   #-}
{-|
Module      : Plugin.Trans.Type
Description : Various functions to get or lift type-related things
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains our various functions to lift types and everything else
that is concerned with loading, dissecting or transforming type-related things.
-}
module Plugin.Trans.Type where

import Data.IORef
import Data.List
import Data.Maybe
import Control.Arrow ( Arrow(first) )

import OccName    hiding (varName)
import HscTypes
import GhcPlugins hiding (substTy, extendTvSubst)
import TyCoRep
import Type
import Finder
import IfaceEnv
import TcRnTypes
import TcRnMonad
import UniqMap
import IfaceSyn
import TcEvidence
import Predicate
import Exception

import Plugin.Trans.Var
import Plugin.Trans.Import

-- This Type contains an IORef, because looking up the mapping between
-- new <-> old type constructors needs IO.
-- We do not want to lookup the full mapping on plugin startup, as
-- we will probably only need a fraction of those anyway
-- | A mapping between the lifted and unlifted version of each type constructor,
-- loaded in lazily.
type TyConMap = ( Env TcGblEnv TcLclEnv
                , TcRef (UniqMap TyCon TyCon, -- Old -> New
                         UniqMap TyCon TyCon, -- New -> Old
                         UniqSet TyCon,       -- Old
                         UniqSet TyCon))      -- New

-- | Get the 'Nondet' monad type constructor.
getMonadTycon :: TcM TyCon
getMonadTycon = getTyCon "Plugin.Effect.Monad" "FL"

getFunTycon :: TcM TyCon
getFunTycon = getTyCon "Plugin.Effect.Monad" "-->"

-- | Get a type constructor from the given module and with the given name.
getTyCon :: String    -- ^ Module name
         -> String    -- ^ TyCon name
         -> TcM TyCon
getTyCon mname name = do
  hscEnv <- getTopEnv
  Found _ mdl <- liftIO $
    findImportedModule hscEnv (mkModuleName mname) Nothing
  lookupTyCon =<< lookupOrig mdl ( mkTcOcc name )

-- | Un-lift a given type. Returns the new type and True iff the type changed.
removeNondet :: Type -> TcM (Type, Bool)
removeNondet = removeNondet' . expandTypeSynonyms
  where
    removeNondet' (ForAllTy b ty) =
      first (ForAllTy b) <$> removeNondet' ty
    removeNondet' (FunTy f ty1 ty2) = do
      (ty1', b1) <- removeNondet' ty1
      (ty2', b2) <- removeNondet' ty2
      return (FunTy f ty1' ty2', b1 || b2)
    removeNondet' (CastTy ty kc) =
      first (`CastTy` kc) <$> removeNondet' ty
    removeNondet' (CoercionTy c) =
      return (CoercionTy c, False)
    removeNondet' (LitTy l) =
      return (LitTy l, False)
    removeNondet' (AppTy ty1 ty2) = do
      (ty1', b1) <- removeNondet' ty1
      (ty2', b2) <- removeNondet' ty2
      return (AppTy ty1' ty2', b1 || b2)
    removeNondet' (TyConApp tc [mty, ty1, ty2]) = do
        ftc <- getFunTycon
        ([ty1', ty2'], bs) <- unzip <$> mapM removeNondet' [ty1, ty2]
        if tc == ftc && mty `eqType` mkTyConTy tc
          then return (FunTy VisArg ty1' ty2', or bs)
          else return (TyConApp tc  [mty, ty1', ty2'], or bs)
    removeNondet' (TyConApp tc [mty, ty]) = do
        mtc <- getMonadTycon
        ftc <- getFunTycon
        if tc == mtc && mty `eqType` mkTyConTy tc
          then removeNondet' ty
          else if tc == ftc && mty `eqType` mkTyConTy tc
            then first (TyConApp funTyCon . (:[])) <$> removeNondet' ty
            else (\(x, b1) (y, b2) -> (TyConApp tc [x, y], b1 || b2)) <$> removeNondet' mty <*> removeNondet' ty
    removeNondet' (TyConApp tc args) = do
      (args', bs) <- unzip <$> mapM removeNondet' args
      return (TyConApp tc args', or bs)
    removeNondet' (TyVarTy v) =
      return (TyVarTy v, False)

{- If we have a type like (T (a -> b)), the correct lifted type is
   ND (TND (ND a -> ND b))
   Note that the function type is NOT lifted, as that lifting is integrated in
   the lifted type constructor ND
   So sometimes we do not want to lift the outermost part of a type that occurs
   somewhere nested.
   This can even occurr in more complex settings
   (T a) (a -> b) should be lifted to
   ND ((TND a) (ND a -> ND b)
   This is why we use liftInnerTy instead of liftType for nested types.

   Normally we want to add Shareable constraints to every type variable,
   using QuantifiedConstraints if possible.
   If this is undesired, use liftTypeNoShareable
-}

-- | Lift a type and add 'Shareable' constraints.
liftTypeTcM :: TyConMap -> Type -> TcM Type
liftTypeTcM tcs ty = do
  mty <- mkTyConTy <$> getMonadTycon
  ftc <- getFunTycon
  us <- getUniqueSupplyM
  liftIO (liftType ftc mty us tcs ty)

-- | Lift a type with the given parameters.
-- If the first parameter is True, add 'Shareable' constraints.
liftType :: TyCon       -- ^ 'Fun' type constructor
         -> Type        -- ^ 'Nondet' type
         -> UniqSupply  -- ^ Fresh supply of unique keys
         -> TyConMap    -- ^ Type constructor map
         -> Type        -- ^ Type to be lifted
         -> IO Type     -- ^ Lifted type
liftType ftc mty s tcs = liftType' s
  where
    liftType' :: UniqSupply -> Type -> IO Type
    liftType' us (ForAllTy b ty) =
      ForAllTy b <$> liftType ftc mty us tcs ty
    -- Types to the left of and invisible function type (=>) are constraints.
    liftType' us (FunTy InvisArg ty1 ty2) =
        FunTy InvisArg <$> liftInnerTy ftc mty s tcs ty1 <*> liftType' us ty2
    -- Wrap a visible function type in our monad, except when it is a
    -- visible dictionary applictation (not possible in GHC yet).-
    liftType' us (FunTy VisArg ty1 ty2)
      | isDictTy ty1 =
        FunTy VisArg <$> liftInnerTy ftc mty s tcs ty1 <*> liftType' us ty2
      | otherwise = do
        let (u1, u2) = splitUniqSupply us
        ty1' <- liftInnerTy ftc mty u1 tcs ty1
        ty2' <- liftInnerTy ftc mty u2 tcs ty2
        return (mkAppTy mty (mkTyConApp ftc [mty, ty1', ty2']))
    liftType' us (CastTy ty kc) =
      flip CastTy kc <$> liftType' us ty
    liftType' _ (CoercionTy c) =
      return (CoercionTy c)
    liftType' _ ty@(LitTy _) =
      return (mkAppTy mty ty)
    -- Lift a type application.
    liftType' us (AppTy ty1 ty2) =
      let (u1, u2) = splitUniqSupply us
      in (mkAppTy mty .) . AppTy
           <$> liftInnerTy ftc mty u1 tcs ty1
           <*> liftInnerTy ftc mty u2 tcs ty2
    -- Lift a type application of a type constructor.
    -- If it is a type class constraint or ANY, do not wrap it with our monad.
    liftType' us (TyConApp tc tys)
      | anyTyCon == tc = return $ TyConApp tc tys
      | isClassTyCon tc = do
        tc' <- lookupTyConMap GetNew tcs tc
        tys' <- mapM (liftInnerTy ftc mty us tcs) tys
        return (TyConApp tc' tys')
      | otherwise       = do
        tc' <- lookupTyConMap GetNew tcs tc
        if tc' == intTyCon
          then return (mkAppTy mty (mkTyConTy intTyCon))
          else do
            tys' <- mapM (liftInnerTy ftc mty us tcs) tys
            return (mkAppTy mty (TyConApp tc' (mty:tys')))
    liftType' _ ty@(TyVarTy _) =
      return (mkAppTy mty ty)

-- | Update type constructors in a pi-type
replacePiTyTcM :: TyConMap -> TyBinder -> TcM TyBinder
replacePiTyTcM tcs b = do
  mtc <- getMonadTycon
  ftc <- getFunTycon
  us <- getUniqueSupplyM
  liftIO (replacePiTy ftc mtc us tcs b)

replacePiTy :: TyCon -> TyCon -> UniqSupply -> TyConMap -> TyBinder
            -> IO TyBinder
replacePiTy _   _   _  _   (Named b   ) = return (Named b)
replacePiTy ftc mtc us tcs (Anon  f t') = Anon f <$> liftInnerTy ftc (mkTyConTy mtc) us tcs t'

-- | Create a type variable with the given kind and unique key.
mkTyVarWith :: Kind -> Unique -> TyVar
mkTyVarWith k u = mkTyVar (mkSystemName u (mkTyVarOcc ("v_" ++ show u))) k

-- | Lift a type if it is not lifted already.
liftTypeIfRequiredTcM :: TyConMap -> Type -> TcM Type
liftTypeIfRequiredTcM tcs ty = do
  mtc <- getMonadTycon
  ftc <- getFunTycon
  us <- getUniqueSupplyM
  liftIO (liftTypeIfRequired ftc mtc us tcs ty)

-- | Lift a type if it is not lifted already.
liftTypeIfRequired :: TyCon -> TyCon -> UniqSupply -> TyConMap -> Type
                   -> IO Type
liftTypeIfRequired ftc mtycon us tcs ty =
  case splitTyConApp_maybe (snd (splitPiTysInvisible ty)) of
    -- The type might already be lifted, if this is a class method
    -- from an imported (non built-in) class
    Just (tc, _) | tc == mtycon -> replaceTyconTy tcs ty
    _                           -> liftType ftc (mkTyConTy mtycon) us tcs ty

-- | Lift a type without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top.
liftInnerTyTcM :: TyConMap -> Type -> TcM Type
liftInnerTyTcM tcs ty = do
  mty <- mkTyConTy <$> getMonadTycon
  ftc <- getFunTycon
  us <- getUniqueSupplyM
  liftIO (liftInnerTy ftc mty us tcs ty)

-- | Lift a type without wrapping it in our monad at the top of the type.
-- Fails if the type has an invisible pi-type (e,.g., forall, constraint)
-- at the top. The function will only add 'Shareable' constraints if
-- the first argument is True.
liftInnerTy :: TyCon       -- ^ 'Fun' type constructor
            -> Type        -- ^ 'Nondet' type
            -> UniqSupply  -- ^ Fresh supply of unique keys
            -> TyConMap    -- ^ Type constructor map
            -> Type        -- ^ Type to be lifted
            -> IO Type     -- ^ Lifted type
liftInnerTy ftc mty us tcs ty = do
  ty' <- liftType ftc mty us tcs ty
  return $ case splitTyConApp_maybe ty' of
    Just (tc, [inner]) | mkTyConTy tc `eqType` mty
      -> inner
    _ -> case splitAppTy_maybe ty' of
      Just (ty1, ty2) | ty1 `eqType` mty -> ty2
      _                                  -> ty'

-- | Replace all type constructors in a type with its lifted version.
replaceTyconTy :: TyConMap -> Type -> IO Type
replaceTyconTy tcs = replaceTyconTy'
  where
    replaceTyconTy' (ForAllTy b ty) =
      ForAllTy b <$> replaceTyconTy' ty
    replaceTyconTy' (FunTy f ty1 ty2) =
      FunTy f <$> replaceTyconTy' ty1 <*> replaceTyconTy' ty2
    replaceTyconTy' (CastTy ty kc) =
      flip CastTy kc <$> replaceTyconTy' ty
    replaceTyconTy' (CoercionTy c) =
      return (CoercionTy c)
    replaceTyconTy' (LitTy l) =
      return (LitTy l)
    replaceTyconTy' (AppTy ty1 ty2) =
      AppTy <$> replaceTyconTy' ty1 <*> replaceTyconTy' ty2
    replaceTyconTy' (TyConApp tc tys) = do
      tc' <- lookupTyConMap GetNew tcs tc
      tys' <- mapM (replaceTyconTy tcs) tys
      return (TyConApp tc' tys')
    replaceTyconTy' (TyVarTy v) =
      return (TyVarTy v)

-- | Lift only the result type of a type.
-- Sometimes (e.g. for records) we only need to lift the result of a type
liftResultTy :: TyCon       -- ^ 'Fun' type constructor
             -> Type        -- ^ 'Nondet' type
             -> UniqSupply  -- ^ Fresh supply of unique keys
             -> TyConMap    -- ^ Type constructor map
             -> Type        -- ^ Type to be lifted
             -> IO Type     -- ^ Lifted type
liftResultTy ftc mty us tcs = liftResultTy'
  where
    liftResultTy' (ForAllTy b ty) =
      ForAllTy b <$> liftResultTy' ty
    liftResultTy' (FunTy f ty1 ty2) =
      FunTy f <$> liftInnerTy ftc mty us tcs ty1 <*> liftResultTy' ty2
    liftResultTy' (CastTy ty kc) =
      flip CastTy kc <$> liftResultTy' ty
    liftResultTy' ty = liftType ftc mty us tcs ty

-- When lifting the type applications in a HsWrapper,
-- we have to remember that the type variables
-- (that are instantiated by this wrapper)
-- are already wrapped in the monadic type.
-- Thus, we use liftInnerTy
-- | Lift the type applications and update type constructors inside a wrapper.
-- Reomves any evidence applications.
liftWrapper :: TyCon        -- ^ 'Fun' type constructor
            -> Type         -- ^ 'Nondet' type
            -> UniqSupply   -- ^ Fresh supply of unique keys
            -> TyConMap     -- ^ Type constructor map
            -> HsWrapper    -- ^ Wrapper to be lifted
            -> IO HsWrapper -- ^ Lifted wrapper
liftWrapper ftc mty us tcs = liftWrapper'
  where
    liftWrapper' (WpCompose w1 w2) =
      WpCompose <$> liftWrapper' w1 <*> liftWrapper' w2
    liftWrapper' (WpFun w1 w2 ty sd) =
      WpFun <$> liftWrapper' w1 <*> liftWrapper' w2
            <*> liftInnerTy ftc mty us tcs ty <*> pure sd
    liftWrapper' (WpCast (SubCo (Refl ty))) =
      WpCast . SubCo . Refl <$> liftInnerTy ftc mty us tcs ty
    liftWrapper' (WpTyApp app) =
      WpTyApp <$> liftInnerTy ftc mty us tcs app
    -- remove any other thing that was here after typechecking
    liftWrapper' _ = return WpHole

-- | Lift the type applications and update type constructors inside a wrapper.
-- Reomves any evidence applications.
liftWrapperTcM :: TyConMap -> HsWrapper -> TcM HsWrapper
liftWrapperTcM tcs w = do
  mty <- mkTyConTy <$> getMonadTycon
  ftc <- getFunTycon
  us <- getUniqueSupplyM
  liftIO (liftWrapper ftc mty us tcs w)

-- | Enumeration of lookup directions for the type constructor map.
data LookupDirection = GetNew -- ^ Look up the lifted version with the unlifted.
                     | GetOld -- ^ Look up the unlifted version with the lifted.
  deriving (Eq, Show)

-- | Look up the other version of a type constructor in the given map
-- or return the argument unchanged if the requested version does not exist.
-- This function lazily loads any new type constructor mappings on demand.
lookupTyConMap :: LookupDirection -> TyConMap -> TyCon -> IO TyCon
lookupTyConMap d (env, ref) tc = do
  -- Get the current state of our map.
  tcs@(mn, mo, sn, so) <- readIORef ref
  -- Establish the correct variables for the given lookup direction.
  let (m, s) = if d == GetNew then (mn, sn) else (mo, so)
  -- Check if we have all the infos for the given TyCon loaded already.
  if tc `elementOfUniqSet` s
    -- Look the TyCon up, with a default fallback.
    then return (lookupWithDefaultUniqMap m tc tc)
    -- Otherwise, get the module of the type constructor if available.
    else case mbMdl of
      -- Check if the module is in the home or external package and load it
      -- from there.
      Just mdl | moduleUnitId mdl == thisPackage flags,
                 not (isOneShot (ghcMode flags))
                  -> lookupTyConHome mdl m s tcs
               | otherwise -> lookupTyConExtern mdl m s tcs
      Nothing -> fail $ "TyCon without module: " ++ show (occNameString (occName n))
  where
    -- | Look up a type constructor replacement from a home package module.
    lookupTyConHome mdl m s tcs = do
      -- Get the module interface
      let miface = lookupIfaceByModule (hsc_HPT hsc) emptyPackageIfaceTable mdl
      -- Get the correct declaration to get the original name.
      case miface >>= (find declFinder . mi_decls) of
        Just (_, f) -- Look up the TyCon with the name and load it into our map.
          -> lookupTypeHscEnv hsc (ifName f) >>= processResult m s tcs
        -- If no correct declaration was found, update our map to remember
        -- that no replacement exists.
        _ -> processResult m s tcs Nothing

    -- | Look up a type constructor replacement from an external package module.
    lookupTyConExtern mdl m s tcs
      | Just mdl' <- lookupSupportedBuiltInModule mdl = do
        let thisMdl = mkModuleName mdl'
        foundMdl <- findImportedModule hsc thisMdl Nothing >>= \case
           Found _ mdl'' -> return mdl''
           _             -> fail $ "Could not find module for built-in type of the imported module: " ++ mdl'
        result <- runIOEnv env (do
          orig <- lookupOrig foundMdl occ2
          Just <$> lookupThing orig) `catch` (\(SomeException _) -> return Nothing)
        case result of
          Just r  -> processResult m s tcs (Just r)
          Nothing -> fail $ "No lifted type available for: " ++ occNameString (occName n)
      | otherwise =  do
        -- Get the table of external packages.
        ext <- eps_PTE <$> readIORef (hsc_EPS hsc)
        -- Find the correct declaration and insert the result into our map.
        let result = fmap snd (find (tyThingFinder mdl occ2) (nonDetUFMToList ext))
        processResult m s tcs result

    -- | Checks if the given declaration uses the name we are looking for.
    declFinder (_, f) = occName (ifName f) == occ2

    -- | Check if the given TyCon uses the name we are looking for.
    tyThingFinder mdl occ (_, ATyCon tc') = occName n' == occ && nameModule_maybe n' == Just mdl
      where n' = tyConName tc'
    tyThingFinder _   _   _               = False

    -- | Insert a lookup result into the correct map on success.
    -- Regardless of success or not, update the set of TyCons that we have
    -- performed a lookup for.
    processResult m s (mn, mo, sn, so) (Just (ATyCon tc'))
      | GetNew <- d = do
        writeIORef ref (addToUniqMap m tc tc', mo, addOneToUniqSet s tc, so)
        return tc'
      | otherwise   = do
        writeIORef ref (mn, addToUniqMap m tc tc', sn, addOneToUniqSet s tc)
        return tc'
    processResult _ s (mn, mo, sn, so) _
      | GetNew <- d = do
        writeIORef ref (mn, mo, addOneToUniqSet s tc, so)
        return tc
      | otherwise   = do
        writeIORef ref (mn, mo, sn, addOneToUniqSet s tc)
        return tc

    hsc = env_top env
    mbMdl = nameModule_maybe n
    flags = hsc_dflags hsc
    n = tyConName tc
    occ2 = case d of
      GetNew -> addNameSuffix (occName n)
      GetOld -> removeNameSuffix (occName n)

-- | Update the type constructors in a type with a pure,
-- side-effect free replacement map.
replaceTyconTyPure :: UniqMap TyCon TyCon -> Type -> Type
replaceTyconTyPure tcs = replaceTyconTy'
  where
    replaceTyconTy' (ForAllTy b ty) =
      ForAllTy b (replaceTyconTy' ty)
    replaceTyconTy' (FunTy f ty1 ty2) =
      FunTy f (replaceTyconTy' ty1) (replaceTyconTy' ty2)
    replaceTyconTy' (CastTy ty kc) =
      CastTy (replaceTyconTy' ty) kc
    replaceTyconTy' (CoercionTy c) =
      CoercionTy c
    replaceTyconTy' (LitTy l) =
      LitTy l
    replaceTyconTy' (AppTy ty1 ty2) =
      AppTy (replaceTyconTy' ty1) (replaceTyconTy' ty2)
    replaceTyconTy' (TyConApp tc tys) =
      let tc' = case lookupUniqMap tcs tc of
                  Just x -> x
                  _      -> tc
      in TyConApp tc' (map replaceTyconTy' tys)
    replaceTyconTy' (TyVarTy v) = TyVarTy v

-- | Remove any outer application of 'Nondet', if available.
-- Can look through type synonyms.
bindingType :: Type -> Type
bindingType (coreView -> Just ty) = bindingType ty
bindingType (TyConApp _ [ty])     = ty
bindingType ty                    = ty

-- Get only the named binders of an invisible pi-type binder.
namedTyBinders :: [TyBinder] -> [TyVarBinder]
namedTyBinders = mapMaybe (\case { Named b -> Just b; Anon _ _ -> Nothing })

-- | Instantiate a type with the given type arguments.
instantiateWith :: [Type] -> Type -> Type
instantiateWith apps ty =
  let (hd, rty) = splitPiTysInvisible ty
      isNamed (Named _) = True
      isNamed _         = False
      (named, anon) = partition isNamed hd
      vs = map binderVar (namedTyBinders named)
      subst = foldr (\(v,a) s -> extendVarEnv s v a)
        emptyTvSubstEnv (zip vs apps)
      in_scope = mkInScopeSet (tyCoVarsOfTypes (ty:apps))
  in substTy (mkTCvSubst in_scope (subst, emptyCvSubstEnv)) (mkPiTys anon rty)

-- | Create a wrapper for the given type with the provided
-- type and evidence applications.
createWrapperFor :: Type -> [Type] -> [Var] -> HsWrapper
createWrapperFor ty apps evids =
  let (hd, _) = splitPiTysInvisible ty
  in wrapperArg hd apps evids
  where
    wrapperArg (Named _ :xs) (a:as) evs    =
      wrapperArg xs as evs <.> WpTyApp a
    wrapperArg (Anon _ _:xs) tvs    (e:es) =
      wrapperArg xs tvs es <.> WpEvApp (EvExpr (evId e))
    wrapperArg _             _      _     =
      WpHole
