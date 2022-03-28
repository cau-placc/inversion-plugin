{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE RecursiveDo       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE LambdaCase        #-}
{-|
Module      : Plugin.InversionPlugin
Description : A GHC plugin to transform GHC into a Curry-Compiler.
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module contains a GHC plugin that turns GHC into a "compiler" for
the functional-logic programming language Curry.
-}
module Plugin.InversionPlugin (plugin, module Plugin.Primitives, module Data.Tuple.Solo) where

import Data.List
import Data.IORef
import Data.Either
import Data.Maybe
import Data.Map.Strict (elems)
import Data.Tuple.Extra (second)
import Data.Tuple.Solo
import Control.Monad.State
import Control.Exception
import Language.Haskell.TH.Syntax
import Language.Haskell.TH  as TH (Type, Kind, Name)

import GHC.Hs
import Plugins
import TcRnTypes
import TcEvidence
import GhcPlugins
import Bag
import TcSimplify
import TcEnv
import TcHsSyn
import TcRnMonad
import UniqMap
import InstEnv
import ErrUtils
import TyCoRep
import IfaceEnv
import PrelNames
import GHC.ThToHs (convertToHsDecls)
import TcRnDriver (tcTopSrcDecls, rnTopSrcDecls)
import Class
import FamInst
import TcTypeable

import Plugin.Dump
import Plugin.Trans.Expr
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.ClsInst
import Plugin.Trans.TyCon
import Plugin.Trans.Record
import Plugin.Trans.Import
import Plugin.Trans.TysWiredIn
import Plugin.Trans.Preprocess
import Plugin.Trans.Class
import Plugin.Trans.Constr
import Plugin.Effect.Annotation
import Plugin.Effect.TH
import Plugin.Trans.Var
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
      let imp = noLoc (ImportDecl noExtField NoSourceText (noLoc impName)
                          Nothing False False NotQualified False
                          Nothing (Just (False, noLoc [])))
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

  -- remove any dummy evidence introduced by the constraint solver plugin
  let tcg_ev_binds' = filterBag (not . isDummyEv) (tcg_ev_binds env)

  fullEnv <- getEnv
  mapRef <- loadDefaultTyConMap
  let tyconsMap = (fullEnv, mapRef)

  -- lift datatypes, we need the result for the lifting of datatypes itself
  s <- getUniqueSupplyM
  mtycon <- getMonadTycon
  ftycon <- getFunTycon
  m <- tcg_mod <$> getGblEnv
  flags <- getDynFlags
  instEnvs <- tcGetFamInstEnvs
  res <- liftIO ((mdo
    liftedTycns <- snd <$>
      mapAccumM (\s' t -> liftTycon flags instEnvs ftycon mtycon s' tnsM tyconsMap t)
        s (tcg_tcs env)
    let tycns = mapMaybe (\(a,b) -> fmap (a,) b) liftedTycns
    let tnsM = listToUniqMap tycns
    return (Right (tycns, liftedTycns)))
    `catch` (return . Left))

  -- extrect results or analyze any thrown IO errors
  (tycons, liftedTycons) <- case res of
    Left e | Just (ClassLiftingException cls reason) <- fromException e
            -> do
              let l = srcLocSpan (nameSrcLoc (getName cls))
              TcRnMonad.reportError (mkErrMsg flags l neverQualify (text reason))
              failIfErrsM
              return ([], [])
           | Just (RecordLiftingException _ p reason) <- fromException e
            -> do
              let l = srcLocSpan (nameSrcLoc (getName p))
              TcRnMonad.reportError (mkErrMsg flags l neverQualify (text reason))
              failIfErrsM
              return ([], [])
           | otherwise
            -> failWith (text ("Unknown error occurred during lifting:" ++
                                displayException e))
    Right r -> return r

  let new = map snd tycons
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
  let anns = tcg_anns env
  let aenv' = extendAnnEnvList aenv [a]
  let anns' = a : anns
  let tenv = plusTypeEnv (tcg_type_env env) (typeEnvFromEntities [] tcg_tcs' [])
  writeTcRef (tcg_type_env_var env) tenv

  let notTypeableBind :: LHsBindLR GhcTc GhcTc -> Bool
      notTypeableBind (L _ (VarBind _ nm _ _)) = let str = occNameString (occName nm)
                                                 in not ("$tc" `isPrefixOf` str || "$trModule" `isPrefixOf` str)
      notTypeableBind _                        = True
  let env0 = env { tcg_tcs        = tcg_tcs'
                 , tcg_type_env   = tenv
                 , tcg_ann_env    = aenv'
                 , tcg_anns       = anns'
                 , tcg_rdr_env    = rdr
                 , tcg_ev_binds   = tcg_ev_binds'
                 , tcg_binds      = filterBag notTypeableBind (tcg_binds env)
                 , tcg_tc_plugins = [] }
  env1 <- setGblEnv env0 mkTypeableBinds -- derive typeable again

  -- set temporary flags needed for all further steps
  -- (enable some language extentions and disable all warnings)
  setDynFlags (flip (foldl wopt_unset) [toEnum 0 ..] $
                foldl xopt_set
                (flags { cachedPlugins = [], staticPlugins = [] }) requiredExtensions) $
    setGblEnv env1 $ do

    invs <- mapM (\(t1, t2) -> do
        t1' <- toTH t1
        t2' <- toTH t2
        liftQ (genInstances t1' t2')) tycons

    ps <- case convertToHsDecls Generated noSrcSpan (concat invs) of
      Right x -> return x
      Left mg -> addErrsTc [mg] >> failIfErrsM >> return []

    dumpWith DumpGenInstances dopts ps

    (env6, rn) <- rnTopSrcDecls (emptyRdrGroup { hs_tyclds = [TyClGroup NoExtField [] [] []
        [L l d | L l (InstD _ d) <- ps] ]} )

    setGblEnv env6 $ do

      ((env7, lcl7), constraints) <- captureConstraints $ tcTopSrcDecls rn
      evBinds <- setGblEnv env7 $ setLclEnv lcl7 $ simplifyTop constraints
      (_, evbinds7, binds7, _, _, _) <- zonkTopDecls evBinds (tcg_binds env7) [] [] []

      dumpWith DumpGenInstancesTyped dopts binds7

      let env3 = env7 { tcg_ev_binds = evbinds7 }
      setGblEnv env3 $ setLclEnv lcl7 $ do
        -- compile pattern matching
        (prep, um) <- runStateT
          (listToBag <$> concatMapM (\(L l bind) -> Prelude.map (L l) <$> preprocessBinding True bind) (bagToList (tcg_binds env1)))
          mempty
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
        let allInsts = tcg_insts env3 ++ newInsts
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

          let rdrEnv = tcg_rdr_env env4

          let thisMdl = tcg_mod env
          let isLocalElt (GRE n _ _ _) = nameIsLocalOrFrom thisMdl n

          {-decs <-  mapM (\nm -> do
                let unliftedStr = occNameString (removeNameSuffix (occName nm))
                case filter isLocalElt $ lookupGlobalRdrEnv rdrEnv (mkVarOcc unliftedStr) of
                  (GRE unliftedNM _ _ _ : _) -> do
                    v <- tcLookupId unliftedNM
                    nE <- externaliseName (tcg_mod env) nm
                    liftQ (genInverses (toTHName m nE) (toTHType m (varType v)) unliftedStr)
                  _ -> panicAny "cannot find unlifted version of lifted decl" nm
              ) (filter (not . isDictFun) umSorted)-}
          let decs = []
          --TODO: cleanup now, because inverses are no longer pre-generated

          psFun <- case convertToHsDecls Generated noSrcSpan (concat decs) of
            Right x -> return x
            Left mg -> addErrsTc [mg] >> failIfErrsM >> return []

          dumpWith DumpInverses dopts psFun

          let isSig (L _ (GHC.Hs.SigD _ _)) = True
              isSig _                       = False

          let (sigs, funs) = partition isSig psFun

          let rdr' = mkGlobalRdrEnv (map (\n -> GRE n NoParent True []) umSorted) `plusGlobalRdrEnv` tcg_rdr_env env4

          let valdemar = ValBinds noExtField
                (listToBag (mapMaybe (\case
                                        L l (GHC.Hs.ValD _ b) -> Just (L l b)
                                        _                     -> Nothing) funs))
                (mapMaybe (\case
                             L l (GHC.Hs.SigD _ si) -> Just (L l si)
                             _                      -> Nothing) sigs)

          let liftedBinds = tcg_binds env4    `unionBags`
                            tcg_bag           `unionBags`
                            listToBag recSelAdd
          (env8, rn') <- setGblEnv (env4 { tcg_binds = liftedBinds, tcg_rdr_env = rdr'}) $
            rnTopSrcDecls (emptyRdrGroup { hs_valds = valdemar })

          let names = [n
                      | HsGroup _ (XValBindsLR (NValBinds _ si)) _ _ _ _ _ _ _ _ _ _ <- [rn']
                      , L _ (TypeSig _ ln _) <- si
                      , L _ n <- ln]


          tenv3 <- readTcRef (tcg_type_env_var env8)
          setGblEnv (env8 { tcg_type_env = tenv3 }) $ do
            ((env9, lcl9), constraints') <- captureConstraints $ tcTopSrcDecls rn'
            evBinds' <- simplifyTop constraints'


            let env10 = env9 { tcg_ev_binds = tcg_ev_binds env9 `unionBags` evBinds' `unionBags` tcg_ev_binds env}
            setGblEnv env10 $ setLclEnv lcl9 $ do

              (tenvfinal, evbindsfinal, bindsfinal, _, _, _) <- zonkTopDecls (tcg_ev_binds env10) (tcg_binds env10) [] [] []

              -- create the final environment with restored plugin field
              let finalEnv = env4 { tcg_binds      = bindsfinal
                                  , tcg_tc_plugins = tcg_tc_plugins env
                                  , tcg_ev_binds   = evbindsfinal
                                  , tcg_exports    = tcg_exports env
                                  , tcg_type_env   = tenvfinal
                                  }

              let keepNames = filter (not . isDictFun) $ umSorted ++ names
              nms <- mapM (externaliseName (tcg_mod env)) keepNames
              liftIO $ modifyIORef (tcg_keep finalEnv)
                          (`extendNameSetList` nms)

              return finalEnv
  where
    liftBindings :: TyConMap -> [(ClsInst, ClsInst)] -> [LHsBindLR GhcTc GhcTc]
                 -> TcM [LHsBindLR GhcTc GhcTc]
    liftBindings y z = fmap (map noLoc) .
      concatMapM (fmap fst . liftMonadicBinding False False [] y z . unLoc)

    isDummyEv (EvBind _ (EvExpr (Var v)) _) =
                  occNameString (occName v) == "#dummy_remove"
    isDummyEv _ = False

toTH :: TyCon -> TcM Dec
toTH tc = do
  m <- tcg_mod <$> getGblEnv
  let tcName' = mkName (occNameString (occName (tyConName tc)))
      bndrs = map (PlainTV . toTHName m . varName) (tyConTyVars tc)
      cons = map (toTHCons m) (tyConDataCons tc)
      synty = toTHType m $ fromJust $ synTyConRhs_maybe tc
  if | isClassTyCon tc -> return $ ClassD [] tcName' bndrs [] []
     | isDataTyCon tc -> return $ DataD [] tcName' bndrs Nothing cons []
     | isNewTyCon tc -> return $ NewtypeD [] tcName' bndrs Nothing (head cons) []
     | isTypeSynonymTyCon tc -> return $ TySynD tcName' bndrs synty
     | otherwise -> panicAny "No family allowed" tc

toTHCons :: GhcPlugins.Module -> DataCon -> Con
toTHCons m dc = NormalC (mkName (occNameString (occName (dataConName dc))))
  [(b, toTHType m t) | t <- dataConOrigArgTys dc]
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
  where (bndrs, ty') = splitPiTysInvisible ty
        (cxt, bndrs') = partitionEithers $ map categorize bndrs
        categorize (Named bndr) = Right (toTHTyVar m (binderVar bndr))
        categorize (Anon _ pty) = Left (toTHType m pty)
toTHType m (FunTy InvisArg ty1 ty2) = case toTHType m ty2 of
  ForallT vs bs ty -> ForallT vs (toTHType m ty1:bs) ty
  ty               -> ForallT [] [toTHType m ty1] ty
toTHType m (FunTy _ ty1 ty2) = mkArrowT (toTHType m ty1) (toTHType m ty2)
toTHType _ (LitTy _) = error "type literals are not supported"
toTHType _ (CastTy _ _) = error "kind casts are not supported"
toTHType _ (CoercionTy _) = error "coercions are not supported"

toTHTyVar :: GhcPlugins.Module -> TyVar -> TyVarBndr
toTHTyVar m tv = KindedTV (toTHName m (varName tv)) (toTHKind m (varType tv))

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
      pkg = unitIdString (moduleUnitId m)
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
        p = GRE n NoParent True []
        conEntries c = GRE (dataConName c) (ParentIs n) True [] :
                       map fieldEntry (dataConFieldLabels c)
        fieldEntry f = GRE (flSelector f) (FldParent n (Just (flLabel f)))
                         True []

-- | Insert the given list of type constructors into the TyConMap.
insertNewTycons :: [(TyCon, Maybe TyCon)]
                -> ( UniqMap TyCon TyCon
                   , UniqMap TyCon TyCon
                   , UniqSet TyCon
                   , UniqSet TyCon )
                -> ( UniqMap TyCon TyCon
                   , UniqMap TyCon TyCon
                   , UniqSet TyCon
                   , UniqSet TyCon )
insertNewTycons = flip (foldr insertNew)
  where
    insertNew (tc, mbtc) (m1, m2, s1, s2) =
      (maybe m1 (addToUniqMap m1 tc) mbtc,
       maybe m2 (flip (addToUniqMap m2) tc) mbtc,
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
