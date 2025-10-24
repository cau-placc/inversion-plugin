{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE RecursiveDo       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf        #-}
{-|
Module      : Plugin.InversionPlugin
Description : A GHC plugin to transform GHC into a Curry-Compiler.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a GHC plugin that turns GHC into a "compiler" for
the functional-logic programming language Curry.
-}
module Plugin.InversionPlugin (plugin, module Plugin.Primitives, module Data.Tuple.Solo, module Plugin.Effect.Monad) where

import Data.List
import Data.IORef
import Data.Either
import Data.Maybe
import Data.Map.Strict as Map (elems, fromList)
import Data.Tuple.Extra (second)
import Data.Tuple.Solo
import Control.Monad.State
import Control.Exception
import Language.Haskell.TH.Syntax as TH

import GHC
import GHC.Core.InstEnv
import GHC.Core.Class
import GHC.Core.TyCo.Rep
import GHC.Data.Bag
import GHC.Plugins as GhcPlugins
import GHC.Tc.Instance.Family
import GHC.Tc.Solver
import GHC.Tc.Types
import GHC.Tc.Utils.Zonk
import GHC.Types.Error
import GHC.Types.SourceText
import GHC.Types.TypeEnv
import GHC.Types.Avail
import GHC.Iface.Env
import GHC.Tc.Utils.Monad as TcRnMonad
import GHC.Tc.Module
import GHC.ThToHs
import GHC.Tc.Instance.Typeable
import GHC.Builtin.Names

import Plugin.Dump
import Plugin.Trans.Expr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.ClsInst
import Plugin.Trans.TyCon
import Plugin.Trans.Import
import Plugin.Trans.TysWiredIn
import Plugin.Trans.Preprocess
import Plugin.Trans.Class
import Plugin.Trans.Constr
import Plugin.Trans.Record
import Plugin.Effect.Annotation
import Plugin.Effect.Monad
import Plugin.Effect.TH
import Plugin.Primitives
import Plugin.Prelude ()


-- | This GHC plugin turns GHC into a "compiler" for
-- the functional-logic programming language Curry.
plugin :: Plugin
plugin = defaultPlugin
  { renamedResultAction   = const processImportPlugin
  , typeCheckResultAction = const . liftMonadPlugin . parseDumpOpts
  , pluginRecompile       = const (return NoForceRecompile)
  , parsedResultAction    = addBuiltinImp
  }
  where
    addBuiltinImp _ _ mdl@HsParsedModule { hpm_module = L l m } = do
      let impName = mkModuleName "Plugin.BuiltIn"
      let imp = noLocA (ImportDecl EpAnnNotUsed NoSourceText (noLocA impName)
                          Nothing NotBoot False NotQualified False
                          Nothing (Just (False, noLocA [])))
      let m' = m { hsmodImports = imp : hsmodImports m}
      return (mdl { hpm_module = L l m'})


-- | This type checker plugin implements the lifting of declarations
-- for the Inversion Plugin.
liftMonadPlugin :: Maybe DumpOpts -> TcGblEnv -> TcM TcGblEnv
liftMonadPlugin mdopts env = do
  dopts <- case mdopts of
    Just xs -> return xs
    Nothing -> addErrTc "Error! Unrecognized plugin option" >>
               failIfErrsM >> return mempty

  dumpWith DumpOriginal        dopts (tcg_binds    env)
  dumpWith DumpOriginalEv      dopts (tcg_ev_binds env)
  dumpWith DumpOriginalInstEnv dopts (tcg_inst_env env)
  dumpWith DumpOriginalTypeEnv dopts (tcg_type_env env)

  fullEnv <- getEnv
  mapRef <- loadDefaultTyConMap
  let tyconsMap = (fullEnv, mapRef)

  -- lift datatypes, we need the result for the lifting of datatypes itself
  s <- getUniqueSupplyM
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  flags <- getDynFlags
  instEnvs <- tcGetFamInstEnvs
  res <- liftIO ((mdo
    liftedTycns <- snd <$>
      mapAccumM (\s' t -> liftTycon flags instEnvs ftycon mtycon s' tnsM tyconsMap t)
        s (tcg_tcs env)
    let tycns = mapMaybe (\(a,b) -> fmap (a,) b) liftedTycns
    let tnsM = listToUFM tycns
    return (Right (tycns, liftedTycns)))
    `catch` (return . Left))

  -- extract results or analyze any thrown IO errors
  (tycons, liftedTycons) <- case res of
    Left e | Just (ClassLiftingException cls reason) <- fromException e
            -> do
              let l = srcLocSpan (nameSrcLoc (getName cls))
              TcRnMonad.reportError (mkMsgEnvelope l neverQualify (text reason))
              failIfErrsM
              return ([], [])
           | Just (RecordLiftingException _ p reason) <- fromException e
            -> do
              let l = srcLocSpan (nameSrcLoc (getName p))
              TcRnMonad.reportError (mkMsgEnvelope l neverQualify (text reason))
              failIfErrsM
              return ([], [])
           | otherwise
            -> failWith (text ("Unknown error occurred during lifting:" ++
                                displayException e))
    Right r -> return r

  let new = map snd tycons

  -- update name cache so that the new names can be found in the interface later on
  forM_ new (\tc -> externaliseName (tcg_mod env) (tyConName tc) >> case tyConRepName_maybe tc of
                Just n  -> void (externaliseName (tcg_mod env) n)
                Nothing -> return ())

  -- The order is important,
  -- as we want to keep t2 if it has the same unique as t1.
  let getRelevant (t1, Just t2) = if t1 == t2 then [t2] else [t1, t2]
      getRelevant (t1, Nothing) = [t1]
  let tcg_tcs' = concatMap getRelevant liftedTycons
  -- insert new tycons mapping into mapRef
  liftIO $ modifyIORef mapRef (insertNewTycons liftedTycons)

  -- insert the new ones into the rename environment
  let rdr = createRdrEnv new `plusGlobalRdrEnv` tcg_rdr_env env

  -- generate module annotation
  let a = Annotation (ModuleTarget (tcg_semantic_mod env))
            (toSerialized serializeWithData Invertible)

  -- update environment and remove tc plugins temporarily
  let aenv = tcg_ann_env env
  let aenv' = extendAnnEnvList aenv [a]
  let anns' = a : tcg_anns env
  let tenv = plusTypeEnv (tcg_type_env env) (typeEnvFromEntities [] tcg_tcs' [] [])
  writeTcRef (tcg_type_env_var env) tenv

  let notTypeableBind :: LHsBindLR GhcTc GhcTc -> Bool
      notTypeableBind (L _ (VarBind _ nm _)) = let str = occNameString (occName nm)
                                               in not ("$tc" `isPrefixOf` str ||
                                                       "$trModule" `isPrefixOf` str ||
                                                       "$krep" `isPrefixOf` str)
      notTypeableBind _                      = True
  let env0 = env { tcg_tcs        = tcg_tcs'
                 , tcg_type_env   = tenv
                 , tcg_ann_env    = aenv'
                 , tcg_anns       = anns'
                 , tcg_rdr_env    = rdr
                 , tcg_binds      = filterBag notTypeableBind (tcg_binds env)
                 , tcg_tc_plugins = [] }
  env1 <- setGblEnv env0 mkTypeableBinds -- derive typeable again

  -- set temporary flags needed for all further steps
  -- (enable some language extentions and disable all warnings)
  setDynFlags (flip (foldl wopt_unset) [toEnum 0 ..] $
                foldl xopt_set
                (flags { pluginModNames = [] }) requiredExtensions) $
    setGblEnv env1 $ do

    invs <- mapM (\(t1, t2) -> do
        t1' <- toTH t1
        t2' <- toTH t2
        liftQ (genInstances t1' t2')) tycons

    ps <- case convertToHsDecls Generated noSrcSpan (concat invs) of
      Right x -> return x
      Left mg -> addErrs [(noSrcSpan, mg)] >> failIfErrsM >> return []

    dumpWith DumpGenInstances dopts ps

    (env6, rn) <- rnTopSrcDecls (emptyRdrGroup { hs_tyclds = [TyClGroup NoExtField [] [] []
        [L l d | L l (InstD _ d) <- ps] ]} )

    setGblEnv env6 $ do

      ((env7, lcl7), constraints) <- captureConstraints $ tcTopSrcDecls rn
      evBinds <- setGblEnv env7 $ setLclEnv lcl7 $ simplifyTop constraints
      (_, evbinds7, binds7, _, _, _) <- zonkTopDecls evBinds (tcg_binds env7) [] [] []

      dumpWith DumpGenInstancesTyped dopts binds7

      let env3 = env7 { tcg_ev_binds = evbinds7 `unionBags` tcg_ev_binds env7 }
      setGblEnv env3 $ setLclEnv lcl7 $ do
        -- for pattern match compilation, we need the rename mapping for default methods from the class lifting
        let extractDef (oldT, newT) = do
              oc <- tyConClass_maybe oldT
              nc <- tyConClass_maybe newT
              let defaultsO = mapMaybe (\(_, mb) -> fst <$> mb) (classOpItems oc)
              let defaultsN = mapMaybe (\(_, mb) -> fst <$> mb) (classOpItems nc)
              return (zipWith ((,) . nameUnique) defaultsO defaultsN)
        let defMethMap = Map.fromList $ concat $ mapMaybe extractDef tycons

        -- compile pattern matching
        (prep, um) <- runStateT
          (listToBag <$> concatMapM (\(L l bind) -> Prelude.map (L l) <$> preprocessBinding False bind) (bagToList (tcg_binds env1)))
          defMethMap
        dumpWith DumpPatternMatched dopts (bagToList prep)

        -- lift instance information
        let origInsts = tcg_insts env
        newInsts <- mapM (liftInstance tyconsMap) origInsts

        let isDictFun v = case occNameString (occName v) of
                            '$':'f':_ -> True
                            '$':'c':_ -> True
                            '$':'d':_ -> True
                            '$':'m':'a':'x':_ -> True
                            '$':'t':'a':'g':_ -> True
                            _         -> False
        let allTopLevel = [ v
                          | L _ (AbsBinds _ _ _ ex _ _ _) <- bagToList prep
                          , ABE _ v _ _ _ <- ex ]
        let (recSelVars, topLevel) = second (map varName) $
                                       partition isRecordSelector allTopLevel

        -- A record selector is special, since it has to remain a record selector during lifting.
        -- But the inverse expects a "properly" lifted function.
        -- Thus, we generate one for each record selector

        recSelAdd <- mapM (mkRecSelFun tyconsMap) recSelVars

        -- hopefully this results in a stable order across recompilations
        let umSorted = sortBy stableNameCmp
                (filter (`elem` topLevel) (elems um) ++
                map is_dfun_name newInsts ++
                [ varName v | tc <- new, Just cls <- [tyConClass_maybe tc], v <- classMethods cls ] ++
                [ varName v | L _ (AbsBinds _ _ _ ex _ _ _) <- recSelAdd, ABE _ v _ _ _ <- ex ])

        -- Remove all instances that were defined in this module
        -- from all instances that were created during compilation,
        -- and replace them with the new instances.
        let allInsts = tcg_insts env3 ++ newInsts -- env3 contains also derived insts
        -- For the environment, we have to keep all external instances,
        -- while replacing all local instances with the new ones.
        -- So we do the same as above,
        -- but use tcg_inst_env instead of tcg_insts.
        let newInstEnv = extendInstEnvList (tcg_inst_env env3) newInsts
        dumpWith DumpInstEnv dopts newInstEnv
        let env4 = env3 { tcg_insts = allInsts
                         , tcg_inst_env = newInstEnv}
        setGblEnv env4 $ do

          -- finally do the monadic lifting for functions and dicts
          tcg_binds' <- liftBindings tyconsMap (zip newInsts origInsts) (bagToList prep)
          let tcg_bag = listToBag $ filter (`keepWithName` umSorted) tcg_binds'

          let rdr' = mkGlobalRdrEnv (map (\n -> GRE (NormalGreName n) NoParent True []) umSorted) `plusGlobalRdrEnv` tcg_rdr_env env4

          let liftedBinds = tcg_binds env4    `unionBags`
                            tcg_bag           `unionBags`
                            listToBag recSelAdd

          tenv3 <- readTcRef (tcg_type_env_var env4)

          let env10 = env4 { tcg_binds = liftedBinds, tcg_rdr_env = rdr', tcg_type_env = tenv3 }
          (tenvfinal, evbindsfinal, bindsfinal, _, _, _) <- zonkTopDecls (tcg_ev_binds env10) (tcg_binds env10) [] [] []

          -- create the final environment with restored plugin field
          let finalEnv = env4 { tcg_binds      = bindsfinal
                              , tcg_tc_plugins = tcg_tc_plugins env
                              , tcg_ev_binds   = evbindsfinal
                              , tcg_exports    = tcg_exports env
                              , tcg_type_env   = tenvfinal
                              }

          let newDataNames = [ AvailTC (tyConName tc')
                                       (map (NormalGreName . dataConName) (tyConDataCons tc') ++
                                       concatMap (map FieldGreName . dataConFieldLabels) (tyConDataCons tc'))
                             | (_, Just tc') <- liftedTycons ]
          let tcwrappers = concat [ map (varName . dataConWrapId) (tyConDataCons tc)
                                  | (_, Just tc) <- liftedTycons ]
          let keepNames = filter (not . isDictFun) umSorted ++
                          concatMap availNames newDataNames ++
                          tcwrappers

          nms <- mapM (externaliseName (tcg_mod env)) keepNames
          liftIO $ modifyIORef (tcg_keep finalEnv)
                      (`extendNameSetList` nms)

          return finalEnv
  where
    liftBindings :: TyConMap -> [(ClsInst, ClsInst)] -> [LHsBindLR GhcTc GhcTc]
                 -> TcM [LHsBindLR GhcTc GhcTc]
    liftBindings y z = fmap (map noLocA) .
      concatMapM (liftMonadicBinding False False [] y z . unLoc)

toTH :: TyCon -> TcM Dec
toTH tc = do
  m <- tcg_mod <$> getGblEnv
  let tcName' = mkName (occNameString (occName (tyConName tc)))
      bndrs = map (flip PlainTV () . toTHName m . varName) (tyConTyVars tc)
      cons = map (toTHCons m) (tyConDataCons tc)
      synty = toTHType m $ fromJust $ synTyConRhs_maybe tc
  if | isClassTyCon tc -> return $ ClassD [] tcName' bndrs [] []
     | isDataTyCon tc -> return $ DataD [] tcName' bndrs Nothing cons []
     | isNewTyCon tc -> return $ NewtypeD [] tcName' bndrs Nothing (head cons) []
     | isTypeSynonymTyCon tc -> return $ TySynD tcName' bndrs synty
     | otherwise -> panicAny "No family allowed" tc

toTHCons :: GhcPlugins.Module -> DataCon -> Con
toTHCons m dc = NormalC (mkName (occNameString (occName (dataConName dc))))
  [(b, toTHType m t) | Scaled _ t <- dataConOrigArgTys dc]
  where
    b = Bang NoSourceUnpackedness NoSourceStrictness

toTHKind :: GhcPlugins.Module -> GhcPlugins.Kind -> TH.Kind
toTHKind = toTHType

toTHType :: GhcPlugins.Module -> GhcPlugins.Type -> TH.Type
toTHType _ t | isLiftedTypeKind t = StarT
toTHType m (TyVarTy tv) = VarT (toTHName m (varName tv))
toTHType m (AppTy ty1 ty2) = AppT (toTHType m ty1) (toTHType m ty2)
toTHType m (TyConApp tc tys)
  | nameUnique (tyConName tc) == typeableClassKey
              =applyType (ConT (toTHName m (tyConName tc))) [toTHType m (last tys)]
  | otherwise = applyType (ConT (toTHName m (tyConName tc))) (map (toTHType m) tys)
toTHType m ty@(ForAllTy _ _) = ForallT bndrs' cxt $ toTHType m ty'
  where (bndrs, ty') = splitInvisPiTys ty
        (cxt, bndrs') = partitionEithers $ map categorize bndrs
        categorize (Named bndr) = Right (toTHTyVar m (binderVar bndr))
        categorize (Anon _ (Scaled _ pty)) = Left (toTHType m pty)
toTHType m (FunTy InvisArg _ ty1 ty2) = case toTHType m ty2 of
  ForallT vs bs ty -> ForallT vs (toTHType m ty1:bs) ty
  ty               -> ForallT [] [toTHType m ty1] ty
toTHType m (FunTy _ _ ty1 ty2) = mkArrowT (toTHType m ty1) (toTHType m ty2)
toTHType _ (LitTy _) = error "type literals are not supported"
toTHType _ (CastTy _ _) = error "kind casts are not supported"
toTHType _ (CoercionTy _) = error "coercions are not supported"

toTHTyVar :: GhcPlugins.Module -> TyVar -> TyVarBndr TH.Specificity
toTHTyVar m tv = KindedTV (toTHName m (varName tv)) TH.SpecifiedSpec (toTHKind m (varType tv))

toTHName :: GhcPlugins.Module -> GhcPlugins.Name -> TH.Name
--toTHName n = mkNameU --mkNameG_tc  (occNameString (occName n)) (NameG ns (mkPkgName pkg) (mkModName modu))
toTHName m' n = case nameModule_maybe n of
  Nothing       -> mkName $ occNameString (occName n) ++ show (nameUnique n)
  Just m
    | m == m'   -> mkName $ occNameString $ occName n
    | otherwise -> mkNameG sp pkg mdl $ occNameString $ occName n
    where
      sp = case occNameSpace (occName n) of
        ns | ns == tcClsName -> TcClsName
           | ns == dataName  -> DataName
           | otherwise       -> VarName
      pkg = unitString (moduleUnit m)
      mdl = moduleNameString (moduleName m)

keepWithName :: LHsBind GhcTc -> [GhcPlugins.Name] -> Bool
keepWithName (L _ b) nm =
  (isAbsBinds b && any (isOk . abe_poly) (abs_exports b)) ||
  (isVarBind  b && isOk (var_id b))
  where isOk v = isRecordSelector v ||
                 (varName v `elem` nm) ||
                 "$c" `isPrefixOf`  occNameString (occName v)

-- | Create a RdrEnv from the given list of type constructors.
-- It can be used to look up names and their origin.
createRdrEnv :: [TyCon] -> GlobalRdrEnv
createRdrEnv = mkGlobalRdrEnv . concatMap createEntries
  where
    createEntries tc = p : concatMap conEntries (tyConDataCons tc)
      where
        n = tyConName tc
        p = GRE (NormalGreName n) NoParent True []
        conEntries c = GRE (NormalGreName (dataConName c)) (ParentIs n) True [] :
                       map fieldEntry (dataConFieldLabels c)
        fieldEntry f = GRE (FieldGreName f) (ParentIs n)
                         True []

-- | Insert the given list of type constructors into the TyConMap.
insertNewTycons :: [(TyCon, Maybe TyCon)]
                -> ( UniqFM TyCon TyCon
                   , UniqFM TyCon TyCon
                   , UniqSet TyCon
                   , UniqSet TyCon )
                -> ( UniqFM TyCon TyCon
                   , UniqFM TyCon TyCon
                   , UniqSet TyCon
                   , UniqSet TyCon )
insertNewTycons = flip (foldr insertNew)
  where
    insertNew (tc, mbtc) (m1, m2, s1, s2) =
      (maybe m1 (addToUFM m1 tc) mbtc,
       maybe m2 (flip (addToUFM m2) tc) mbtc,
       addOneToUniqSet s1 tc,
       maybe s2 (addOneToUniqSet s2) mbtc)

-- | Extensions that are required by the plugin.
requiredExtensions :: [Extension]
requiredExtensions =
  [ FlexibleInstances
  , FlexibleContexts
  , KindSignatures
  , MonoLocalBinds
  , ScopedTypeVariables
  , TypeFamilies
  , UndecidableInstances
  , IncoherentInstances
  , EmptyCase
  , MultiParamTypeClasses
  ]
