{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

-- |
-- Module      : Plugin.Trans.Expr
-- Description : Main lifting transformation for functions and expressions
-- Copyright   : (c) Kai-Oliver Prott (2020)
-- Maintainer  : kai.prott@hotmail.de
--
-- This module provides the main transformation of our monadic lifting for
-- functions and expressions to integrate our effect.
module Plugin.Trans.Expr (liftMonadicBinding, liftMonadicExpr) where

import Control.Monad
import Data.Char
import Data.List
import Data.Maybe
import Data.Generics.Aliases
import Data.Generics.Schemes
import Data.Tuple.Extra
import Data.Data (Data)

import GHC.Builtin.Names
import GHC.Builtin.PrimOps
import GHC.Builtin.Types.Prim
import GHC.Core.Class
import GHC.Core.ConLike
import GHC.Core.InstEnv
import GHC.Core.TyCo.Rep
import GHC.Data.Bag
import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Hs.Lit
import GHC.Hs.Pat
import GHC.Hs.Type
import GHC.Iface.Env
import GHC.Int
import GHC.Parser.Annotation
import GHC.Plugins
import GHC.Tc.Solver
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Types.Origin
import GHC.Tc.Utils.Env
import GHC.Tc.Utils.Monad
import GHC.Tc.Utils.TcMType
import GHC.Tc.Utils.TcType
import GHC.Tc.Utils.Zonk
import GHC.Types.Id.Make
import GHC.Types.Tickish
import GHC.Types.TypeEnv
import GHC.Types.TyThing
import GHC.Utils.Error
import Language.Haskell.Syntax.Extension
import Plugin.Trans.Class
import Plugin.Trans.Coerce
import Plugin.Trans.Constr
import Plugin.Trans.CreateSyntax
import Plugin.Trans.DictInstFun
import Plugin.Trans.FunWiredIn
import Plugin.Trans.Pat
import Plugin.Trans.Record
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Effect.Monad

-- | Transform the given binding with a monadic lifting to incorporate
-- our nondeterminism as an effect.
-- This function also transforms any nested bindings recursively and
-- thus needs to know whether it is a local binding or not.
-- First  Bool: This is a local binding, swap the Unique for sharing purposes
-- Second Bool: This is a nested AbsBinds, do not insert into type env
liftMonadicBinding ::
  Bool ->
  Bool ->
  [Ct] ->
  TyConMap ->
  [(ClsInst, ClsInst)] ->
  HsBindLR GhcTc GhcTc ->
  TcM ([HsBindLR GhcTc GhcTc], [(Var, LocatedN Var)])
liftMonadicBinding _ _ given tcs _ (FunBind wrap (L b name) eqs ticks) =
  setSrcSpanA b $
    addLandmarkErrCtxt ("In the definition of" <+> ppr name) $ do
      -- create the dictionary variables
      let (tvs, c) = collectTyDictArgs wrap
      stc <- getShareClassTycon
      mtc <- getMonadTycon
      let mty = mkTyConTy mtc
      uss <- replicateM (length tvs) getUniqueSupplyM
      let mkShareTy ty = mkTyConApp stc [mty, ty]
      let evsty =
            catMaybes $
              zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss tvs
      evs <- mapM freshDictId evsty
      lclEnv <- getLclEnv
      let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv

      allEvs <- (++ evs) <$> liftIO (mapM replaceEv c)
      let cts = mkGivens ctloc allEvs
      let given' = given ++ cts
      let unlifted = varType name
      ty <- liftTypeTcM tcs unlifted
      let name' = setVarType name ty
      let wrapLike = createWrapperLike ty tvs allEvs

      (eqs', con) <-
        captureConstraints $
          liftMonadicEquation given' tcs eqs
      lvl <- getTcLevel
      env <- getLclEnv
      u <- getUniqueM
      ref1 <- newTcRef emptyEvBindMap
      ref2 <- newTcRef emptyVarSet
      let bindsVar = EvBindsVar u ref1 ref2

      let impls = mkImplications given' tvs lvl env bindsVar con
      simplifyTopImplic impls
      zEnv <- emptyZonkEnv
      binds' <- snd <$> zonkTcEvBinds zEnv (TcEvBinds bindsVar)

      let fullwrap = wrapLike <.> mkWpLet binds'
      ticks' <- mapM (liftTick tcs) ticks
      return ([FunBind fullwrap (L b name') eqs' ticks'], [])
  where
    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)
liftMonadicBinding lcl _ given tcs _ (AbsBinds a b c d e f g)
  -- we do not want to lift dicts or record selectors or other system stuff here
  | all (noSystemNameOrRec . abe_poly) d = do
      -- create the dictionary variables
      stc <- getShareClassTycon
      mty <- mkTyConTy <$> getMonadTycon
      uss <- replicateM (length b) getUniqueSupplyM
      let mkShareTy ty = mkTyConApp stc [mty, ty]
      let evsty =
            catMaybes $
              zipWith ((. flip Bndr Inferred) . mkShareable mkShareTy) uss b
      evs <- mapM freshDictId evsty
      lclEnv <- getLclEnv
      let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv

      allEvs <- (++ evs) <$> liftIO (mapM replaceEv c)
      let cts = mkGivens ctloc allEvs
      let given' = given ++ cts

      (d', vs) <- unzip <$> mapM liftEx d
      let vs' = catMaybes vs

      -- lift inner bindings
      let bs = map unLoc (bagToList f)
      f' <-
        listToBag . map noLocA . concat
          <$> mapM
            (fmap fst . liftMonadicBinding lcl True given' tcs [])
            (foldr (\(n, o, _) -> substitute n o) bs vs')

      -- lift any original evidence that is exported. This is only relevant
      -- for standalone AbsBinds that bind any class parent dictionary
      e' <-
        mapM
          (liftEvidence given' tcs)
          (filter isExportedEv (concatMap flattenEv e))
      vs'' <-
        mapM
          ( \(v1, v2, v3) ->
              (,,v3)
                <$> (setVarType v1 <$> liftTypeTcM tcs (varType v1))
                <*> (setVarType v2 <$> liftTypeTcM tcs (varType v2))
          )
          vs'
      return ([AbsBinds a b allEvs d' e' f' g], map (getLocFrom bs) vs'')
  where
    bindingVarMaybe :: HsBindLR GhcTc GhcTc -> Maybe (LocatedN Var)
    bindingVarMaybe (FunBind _ name _ _) = Just name
    bindingVarMaybe _ = Nothing

    getLocFrom [] _ = error "Variable does not exist"
    getLocFrom (x : xs) (v1, v2, v3)
      | Just (L l name) <- bindingVarMaybe x,
        name == v3 =
          (v1, L l v2)
      | otherwise = getLocFrom xs (v1, v2, v3)

    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)

    -- Basically do the same as in liftTopTypes, but this time for
    -- both the poly and mono type and for local bindings as well
    liftEx :: ABExport GhcTc -> TcM (ABExport GhcTc, Maybe (Var, Var, Var))
    liftEx (ABE x v1 v2 w p) = do
      -- change unique only for local decls, as only those are shared
      u <- if lcl then getUniqueM else return (varUnique v1)

      -- lift types
      mtycon <- getMonadTycon
      ftycon <- getFunTycon
      stycon <- getShareClassTycon
      us2 <- getUniqueSupplyM

      -- We only want to introduce Shareable constraints for the type
      -- variables bound in this AbsBind, so we manually split off
      -- all type and evidence abstractions bound here.
      -- Then we can do the lifting and stuff.
      -- All of this is only done, when a lifting is even required.
      let v1ty = varType v1
      ty1 <- do
          let (bs1, t1) = splitInvisPiTysN (length b + length c) v1ty
          let bs = mapMaybe namedTyCoVarBinder_maybe bs1
          uss <- replicateM (length bs) getUniqueSupplyM
          let mkShareType t' = mkTyConApp stycon [mkTyConTy mtycon, t']
              cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
          bs1' <- mapM (replacePiTyTcM tcs) bs1
          mkPiTys bs1' . flip (foldr mkInvisFunTyMany) cons
            <$> liftTypeTcM tcs t1

      -- The wrapper w deals with matching the impedence beteween the expected
      -- type of the exported function and the real type that is dictated by
      -- the type and evidence variables.
      -- See note [ABExport wrapper] in GHC.Hs.Binds.
      -- In addition to matching the type applications of the function,
      -- We also have to match the Shareable dictionaries
      -- that have been inserted.
      let (vs, rest) = collectHsWrapBinders w
          vswrap = foldr ((<.>) . WpTyLam) WpHole vs
          bs = map (flip Bndr Inferred) vs
          mkShareType t' = mkTyConApp stycon [mkTyConTy mtycon, t']
      uss <- replicateM (length vs) getUniqueSupplyM
      let cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
      convs <- mapM freshDictId cons
      let conwrap = foldr (flip (<.>) . WpEvLam) vswrap (reverse convs)
      -- For unused types, we can just apply GHC.Types.Any to them.
      -- For unused evidence, we cannot do this.
      -- Instead we create dummy evidence terms that have the right type
      -- by using unsafeCoerce.
      -- We know that the evidence is unused,
      -- because its type is Shareable Nondet Any.
      dfl <- getDynFlags
      let unsafeCoShare =
            Cast
              (mkIntExpr (targetPlatform dfl) 0)
              ( mkUnivCo
                  (PluginProv "unsafe")
                  Representational
                  intTy
                  (mkShareType (anyTypeOfKind liftedTypeKind))
              )
      let ovs = repeat unsafeCoShare
      let evs = reverse $ zipWith ((,) . mkTyVarTy) vs convs
      let conapp = mkEvWrapSimilar rest ovs evs

      -- lift the mono type and create the new variables.
      ty2 <- liftIO (liftTypeIfRequired stycon ftycon mtycon us2 tcs (varType v2))
      let v2' = setVarType v2 ty2
      let v1' = setVarType v1 ty1
      -- also (possibly) change unique for sharing
      let v1u = setVarUnique v1' u
      return
        ( ABE x v1u v2' (conwrap <.> (conapp <.> rest)) p,
          Just (setVarUnique v1 u, v1, v2)
        )

    -- Do not lift any system stuff, except instance fun definitions ($c) and
    -- class default methods ($dm).
    noSystemNameOrRec v = case occNameString (occName v) of
      n
        | "$con2tag_" `isPrefixOf` n -> True
        | "$maxtag" `isPrefixOf` n -> True
        | "$tag2con" `isPrefixOf` n -> True
      '$' : 'c' : _ -> True
      '$' : 'd' : 'm' : _ -> True
      '$' : xs@(_ : _) | any isAlpha xs -> False
      _ -> not (isRecordSelector v)

    flattenEv (TcEvBinds _) = []
    flattenEv (EvBinds ebs) = bagToList ebs
    isExportedEv (EvBind v _ _) = any ((== v) . abe_mono) d
liftMonadicBinding _ _ _ tcs clsInsts bind@(AbsBinds _ _ _ d _ _ _)
  | all (isDictFun . abe_poly) d =
      maybe ([bind], []) ((,[]) . (: []))
        <$> liftDictInstFun bind tcs clsInsts
  where
    isDictFun v = case occNameString (occName v) of
      '$' : 'f' : _ -> True
      _ -> False
liftMonadicBinding _ _ _ tcs _ bind@(AbsBinds _ _ _ d _ _ _)
  | all (isRecordSelector . abe_poly) d =
      maybe ([bind], []) ((,[]) . (: [bind])) -- do not throw away the old selector
        <$> liftRecordSel tcs bind
liftMonadicBinding _ _ _ tcs _ (VarBind x1 name e1)
  -- This is the error binding for an unimplemented type class function.
  -- Anything like $c... = noMethodBindingError @ 'LiftedRep @ ty "..."#,
  | '$' : 'c' : _ <- occNameString (occName name) = do
      let (wrap, e1') = case e1 of
            L _ (XExpr (WrapExpr (HsWrap w e))) -> (w, e)
            L _ e -> (WpHole, e)
      case e1' of
        HsApp x2 (L l3 (XExpr (WrapExpr (HsWrap (WpCompose w1 w2) e2)))) e3 -> do
          mtycon <- getMonadTycon
          stycon <- getShareClassTycon
          -- Look at the number of abstractions in wrap.
          -- Those abstractions correspond to the vars bound in the instance head.
          -- Only for those we want Shareable.
          -- But only if the type is not lifted already.
          let numBinders = length (fst (collectHsWrapBinders wrap))
          let ty = varType name
          (ty', bndrs) <- case splitTyConApp_maybe (snd (splitInvisPiTys ty)) of
            Just (tc, _)
              | tc == mtycon ->
                  (,[]) <$> liftIO (replaceTyconTy tcs ty)
            _ -> do
              let (bs1, ty1) = splitInvisPiTysN numBinders ty
                  bs = mapMaybe namedTyCoVarBinder_maybe bs1
              uss <- replicateM (length bs) getUniqueSupplyM
              let mkShareType t' = mkTyConApp stycon [mkTyConTy mtycon, t']
                  cons = catMaybes $ zipWith (mkShareable mkShareType) uss bs
              bs1' <- mapM (replacePiTyTcM tcs) bs1
              (,cons) . mkPiTys bs1' . flip (foldr mkInvisFunTyMany) cons
                <$> liftTypeTcM tcs ty1

          let name' = setVarType name ty'
          wrap' <- createAbstractionWrapperWith wrap bndrs
          w1' <- liftErrorWrapper tcs w1
          w2' <- liftErrorWrapper tcs w2
          let e1'' = HsApp x2 (L l3 (mkHsWrap (WpCompose w1' w2') e2)) e3
          return ([VarBind x1 name' (noLocA (mkHsWrap wrap' e1''))], [])
        _ -> panicAny "Unexpected layout of unimplemented method error expr" e1'
liftMonadicBinding _ _ _ _ _ a = return ([a], [])

-- The variables introduced here are guaranteed to be unused.
-- We just need to match the expected type.
createAbstractionWrapperWith :: HsWrapper -> [Type] -> TcM HsWrapper
createAbstractionWrapperWith w [] = return w
createAbstractionWrapperWith w (ty : tys) = do
  v <- freshDictId ty
  createAbstractionWrapperWith (w <.> WpEvLam v) tys

liftEvidence :: [Ct] -> TyConMap -> EvBind -> TcM TcEvBinds
liftEvidence given tcs (EvBind v _ _) = do
  -- Re-create constraints with the lifted constraint type
  -- This is only used for class parent dictionaries,
  -- so this is never a coercion that needs to be solved
  ty <- liftTypeTcM tcs (varType v)
  loc <- getCtLocM (OccurrenceOf (varName v)) Nothing
  let dst = EvVarDest (setVarType v ty)
  let cts = [CNonCanonical (CtWanted ty dst WDeriv loc)]
  -- solve them
  EvBinds <$> simplifyTop (WC (listToBag (cts ++ given)) emptyBag emptyBag)

liftLocalBinds ::
  [Ct] ->
  TyConMap ->
  HsLocalBinds GhcTc ->
  TcM (HsLocalBinds GhcTc, [(Var, LocatedN Var)])
liftLocalBinds given tcs (HsValBinds x b) = do
  (b', vs) <- liftValBinds given tcs b
  return (HsValBinds x b', vs)
liftLocalBinds _ _ b@(HsIPBinds _ _) = do
  reportError
    ( mkMsgEnvelope
        noSrcSpan
        neverQualify
        "Implicit parameters are not supported by the plugin"
    )
  failIfErrsM
  return (b, [])
liftLocalBinds _ _ b = return (b, [])

liftValBinds ::
  [Ct] ->
  TyConMap ->
  HsValBindsLR GhcTc GhcTc ->
  TcM (HsValBindsLR GhcTc GhcTc, [(Var, LocatedN Var)])
liftValBinds _ _ bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
liftValBinds given tcs (XValBindsLR (NValBinds bs _)) = do
  (bs', vss) <- unzip <$> mapM liftNV bs
  return (XValBindsLR (NValBinds bs' []), concat vss)
  where
    liftNV ::
      (RecFlag, LHsBinds GhcTc) ->
      TcM ((RecFlag, LHsBinds GhcTc), [(Var, LocatedN Var)])
    liftNV (rf, b) = do
      let bs1 = map unLoc (bagToList b)
      (bs2, vss) <-
        first (map noLocA . concat) . unzip
          <$> mapM (liftMonadicBinding True False given tcs []) bs1
      return ((rf, listToBag bs2), concat vss)

liftMonadicEquation ::
  [Ct] ->
  TyConMap ->
  MatchGroup GhcTc (LHsExpr GhcTc) ->
  TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftMonadicEquation given tcs (MG a (L b alts) c) = do
  a'@(MatchGroupTc _ res) <- liftMGTc tcs a
  alts' <- mapM (liftMonadicAlt given tcs res) alts
  return (MG a' (L b alts') c)

liftMGTc :: TyConMap -> MatchGroupTc -> TcM MatchGroupTc
liftMGTc tcs (MatchGroupTc args res) = do
  res' <- liftTypeTcM tcs res
  args' <- mapM (\(Scaled m ty) -> Scaled m <$> liftTypeTcM tcs ty) args
  return (MatchGroupTc args' res')

liftMonadicAlt ::
  [Ct] ->
  TyConMap ->
  Type ->
  LMatch GhcTc (LHsExpr GhcTc) ->
  TcM (LMatch GhcTc (LHsExpr GhcTc))
liftMonadicAlt given tcs resty (L a (Match b c d rhs)) = do
  (d', s) <- unzip <$> mapM (liftPattern tcs) d
  rhs' <- liftMonadicRhs (concat s) given tcs resty rhs
  return (L a (Match b c d' rhs'))

liftMonadicRhs ::
  [(Var, LocatedN Var)] ->
  [Ct] ->
  TyConMap ->
  Type ->
  GRHSs GhcTc (LHsExpr GhcTc) ->
  TcM (GRHSs GhcTc (LHsExpr GhcTc))
liftMonadicRhs s given tcs resty (GRHSs a grhs b) = do
  grhs' <- mapM (liftMonadicGRhs s given tcs resty) grhs
  return (GRHSs a grhs' b)

liftMonadicGRhs ::
  [(Var, LocatedN Var)] ->
  [Ct] ->
  TyConMap ->
  Type ->
  LGRHS GhcTc (LHsExpr GhcTc) ->
  TcM (LGRHS GhcTc (LHsExpr GhcTc))
liftMonadicGRhs s given tcs bdyty (L a (GRHS b c body)) = do
  body' <- liftMonadicExpr given tcs body
  L a . GRHS b c <$> shareVars tcs s given body' bdyty

liftMonadicExpr ::
  [Ct] ->
  TyConMap ->
  LHsExpr GhcTc ->
  TcM (LHsExpr GhcTc)
liftMonadicExpr given tcs (L _ (HsVar _ (L _ v))) = do
  dtt <- tcLookupId =<< lookupOrig gHC_PRIM (mkVarOcc "dataToTag#")
  liftVarWithWrapper given tcs WpHole v (varUnique dtt)
liftMonadicExpr given tcs (L _ (XExpr (WrapExpr (HsWrap w (HsVar _ (L _ v)))))) = do
  dtt <- tcLookupId =<< lookupOrig gHC_PRIM (mkVarOcc "dataToTag#")
  liftVarWithWrapper given tcs w v (varUnique dtt)
liftMonadicExpr _ _ e@(L _ (HsLit _ (HsIntPrim _ _))) = do
  conE <- liftQ [|I#|]
  let conty = mkVisFunTyMany intPrimTy intTy
  lit <- mkApp (mkNewAny conE) conty [e]
  mkApp mkNewReturnTh intTy [noLocA (HsPar EpAnnNotUsed lit)]
liftMonadicExpr _ tcs e@(L _ HsLit {}) = do
  ty <- getTypeOrPanic e -- ok
  ty' <- liftInnerTyTcM tcs ty
  res <- mkApp (mkNewtoFLTh ty) ty' [e]
  return $ noLocA $ HsPar EpAnnNotUsed res
liftMonadicExpr given tcs (L l (HsOverLit _ lit)) =
  case ol_witness lit of
    -- if this is geniunely a Double or Float, just wrap it with return
    e@(HsApp _ (L _ (HsConLikeOut _ (RealDataCon dc))) _)
      | dc == doubleDataCon || dc == floatDataCon -> do
          ty <- getTypeOrPanic (noLocA e) -- ok
          mkApp mkNewReturnTh ty [noLocA e]
    -- otherwise, just lift the witness
    _ -> liftMonadicExpr given tcs (L l (ol_witness lit))
liftMonadicExpr given tcs (L l (HsLam _ mg)) =
  liftLambda given tcs l Nothing mg
liftMonadicExpr given tcs (L l (HsLamCase _ mg)) =
  liftLambda given tcs l Nothing mg
liftMonadicExpr _ tcs (L _ (HsConLikeOut _ (RealDataCon c)))
  | c == intDataCon = do
      idExp <- liftQ [|return id|]
      mtycon <- getMonadTycon
      let ty =
            mkTyConApp
              mtycon
              [ mkTyConApp mtycon [intTy]
                  `mkVisFunTyMany` mkTyConApp mtycon [intTy]
              ]
      mkApp (mkNewAny idExp) ty []
  | otherwise = do
      c' <- liftIO (getLiftedCon c tcs)
      let tys = dataConOrigArgTys c'
      let stricts = dataConImplBangs c'
      e <- fst <$> mkConLam Nothing c' (zip tys stricts) []
      return $ noLocA $ HsPar EpAnnNotUsed e
liftMonadicExpr _ tcs (L _ (XExpr (WrapExpr (HsWrap w (HsConLikeOut _ (RealDataCon c))))))
  | c == intDataCon = do
      idExp <- liftQ [|return id|]
      mtycon <- getMonadTycon
      let ty =
            mkTyConApp
              mtycon
              [ mkTyConApp mtycon [intTy]
                  `mkVisFunTyMany` mkTyConApp mtycon [intTy]
              ]
      mkApp (mkNewAny idExp) ty []
  | otherwise = do
      c' <- liftIO (getLiftedCon c tcs)
      w' <- liftWrapperTcM True tcs w
      let (apps, absts) = collectTyApps w'
          realApps = drop (length absts) apps
      mty <- mkTyConTy <$> getMonadTycon
      let tys = conLikeInstOrigArgTys (RealDataCon c') (mty : realApps)
      let stricts = dataConImplBangs c'
      e <- fst <$> mkConLam (Just w') c' (zip tys stricts) []
      return $ noLocA $ HsPar EpAnnNotUsed e
liftMonadicExpr given tcs (L _ (OpApp _ e1 op e2)) = do
  -- e1 `op` e2
  -- -> (op `appFL` e1) `appFL` e2
  opty1 <- getTypeOrPanic op >>= liftTypeTcM tcs -- ok
  e1' <- liftMonadicExpr given tcs e1
  op' <- liftMonadicExpr given tcs op
  e2' <- liftMonadicExpr given tcs e2
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let (argty1, opty2) = splitMyFunTy ftc mtc $ bindingType opty1
  let (argty2, _) = splitMyFunTy ftc mtc $ bindingType opty2
  e1'' <- mkFuncApp given op' opty1 e1' argty1
  let bracketed = noLocA (HsPar EpAnnNotUsed e1'')
  e2'' <- mkFuncApp given bracketed opty2 e2' argty2
  return $ noLocA $ HsPar EpAnnNotUsed e2''
liftMonadicExpr given tcs (L _ (HsApp _ fn ex)) = do
  -- e1 e2
  -- -> e1 `appFL` e2
  fn' <- liftMonadicExpr given tcs fn
  ex' <- liftMonadicExpr given tcs ex
  funty <- getTypeOrPanic fn >>= liftTypeTcM tcs
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let (argty, _) = splitMyFunTy ftc mtc $ bindingType funty
  res <- mkFuncApp given fn' funty ex' argty
  return $ noLocA $ HsPar EpAnnNotUsed res
liftMonadicExpr given tcs (L _ (HsAppType _ e _)) =
  liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (NegApp _ e (SyntaxExprTc n ws w))) =
  liftMonadicExpr
    given
    tcs
    ( L
        l
        ( mkHsWrap
            w
            (HsApp EpAnnNotUsed (noLocA n) (fmap (mkHsWrap (head ws)) e))
        )
    )
liftMonadicExpr _ _ (L _ (NegApp _ _ NoSyntaxExprTc)) = undefined
liftMonadicExpr given tcs (L l (HsPar x e)) =
  L l . HsPar x <$> liftMonadicExpr given tcs e
liftMonadicExpr _ _ e@(L _ (SectionL _ _ _)) = do
  panicAny "Sections should have been desugared by GHC already" e
liftMonadicExpr _ _ e@(L _ (SectionR _ _ _)) =
  panicAny "Sections should have been desugared by GHC already" e
liftMonadicExpr given tcs (L _ (ExplicitTuple _ args b)) =
  liftExplicitTuple given tcs args b
liftMonadicExpr _ _ e@(L _ ExplicitSum {}) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Unboxed sum types are not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsCase _ scr br)) = do
  br'@(MG (MatchGroupTc _ ty2) _ _) <- liftMonadicEquation given tcs br
  scr' <- liftMonadicExpr given tcs scr
  ty1 <- getTypeOrPanic scr >>= liftTypeTcM tcs -- ok
  let cse = L l $ HsLamCase EpAnnNotUsed br'
  mkBind given scr' ty1 (noLocA $ HsPar EpAnnNotUsed cse) ty2
liftMonadicExpr given tcs (L l (HsIf _ e1 e2 e3)) = do
  -- if e1 then e2 else e3
  -- -> e1 >>= \case { True -> e2; _ -> e3 }
  e1' <- liftMonadicExpr given tcs e1
  e2' <- liftMonadicExpr given tcs e2
  e3' <- liftMonadicExpr given tcs e3
  ty1' <- getTypeOrPanic e1 >>= liftTypeTcM tcs -- ok
  ty2' <- getTypeOrPanic e2 >>= liftTypeTcM tcs -- ok
  let ty1 = bindingType ty1'
  v <- noLocA <$> freshVar (Scaled Many ty1)
  conv <- mkNewBoolConversion
  let ife = HsIf noExtField (mkHsApp conv (noLocA (HsVar noExtField v))) e2' e3'
  let alt = mkSimpleAlt LambdaExpr (noLocA ife) [noLocA (VarPat noExtField v)]
  let mgtc = MatchGroupTc [Scaled Many ty1] ty2'
  let mg = MG mgtc (noLocA [noLocA alt]) Generated
  mkBind given e1' ty1' (noLocA $ HsPar EpAnnNotUsed $ L l $ HsLam noExtField mg) ty2'
liftMonadicExpr _ _ e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
liftMonadicExpr given tcs (L l (HsLet x bs e)) = do
  -- Lift local binds first, so that they end up in the type environment.
  (bs', vs) <- liftLocalBinds given tcs bs
  e' <- liftMonadicExpr given tcs e
  ety <- getTypeOrPanic e >>= liftTypeTcM tcs -- ok
  e'' <- shareVars tcs vs given e' ety
  return (L l (HsLet x bs' e''))
liftMonadicExpr given tcs (L l1 (HsDo x ctxt (L l2 stmts))) = do
  x' <- liftTypeTcM tcs x
  -- Because ListComp are not overloadable,
  -- we have to change them to MonadComp.
  let ctxtSwitch
        | ListComp <- ctxt = True
        | otherwise = False
  let ctxt'
        | ctxtSwitch = MonadComp
        | otherwise = ctxt
  stmts' <- liftMonadicStmts ctxt' ctxtSwitch x' given tcs stmts
  return (L l1 (HsDo x' ctxt' (L l2 stmts')))
liftMonadicExpr given tcs (L _ (ExplicitList ty es)) = do
  -- [e1, ..., en]
  -- -> return (Cons e1 (return (Cons ... (return (Cons en (return Nil))))))
  ty' <- liftInnerTyTcM tcs ty
  em <- mkEmptyList ty' tcs
  liftedTy <- liftInnerTyTcM tcs (mkListTy ty) -- ok
  nil <- mkApp mkNewReturnTh liftedTy [em]
  if null es
    then return nil
    else do
      es' <- mapM (liftMonadicExpr given tcs) es
      cons <- mkConsList ty' tcs
      let mkCons e1 e2 =
            let e' = mkHsApp (mkHsApp cons e1) e2
             in mkApp mkNewReturnTh liftedTy [e']
      foldrM mkCons nil es'
liftMonadicExpr given tcs (L l1 (RecordCon ce (L l2 (RealDataCon c)) fs)) = do
  c' <- liftIO (getLiftedCon c tcs)
  ce' <- liftConExpr tcs c' ce
  fs' <- liftMonadicRecFields given tcs fs
  let e = L l1 (RecordCon ce' (L l2 (RealDataCon c')) fs')
  if isNewTyCon (dataConTyCon c')
    then return e
    else getTypeOrPanic e >>= flip (mkApp mkNewReturnTh) [e] -- ok
liftMonadicExpr _ _ e@(L _ (RecordCon _ (L _ (PatSynCon _)) _)) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Pattern synonyms are not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (RecordUpd rtc e fs)) = do
  rtc'@(RecordUpdTc (c : _) inty outty _) <- liftMonadicRecordUpd tcs rtc
  e' <- liftMonadicExpr given tcs e
  fs' <-
    either
      (fmap Left . mapM (liftMonadicRecordUpdField given tcs))
      (fmap Right . mapM (liftMonadicRecordProjField given tcs))
      fs
  let vty = conLikeResTy c inty
  v <- noLocA <$> freshVar (Scaled Many vty)
  let upd = L l (RecordUpd rtc' (noLocA (HsVar noExtField v)) fs')
  let updTy = conLikeResTy c outty
  let updLam = mkLam v (Scaled Many vty) upd updTy
  mkApp (mkNewFmapTh vty) updTy [updLam, e']
liftMonadicExpr given tcs (L _ (ExprWithTySig _ e _)) =
  liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L _ (ArithSeq x Nothing i)) =
  liftMonadicExpr given tcs (foldl mkHsApp (noLocA x) (arithSeqArgs i))
liftMonadicExpr _ _ e@(L _ (ArithSeq _ (Just _) _)) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Overloaded lists are not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsPragE x (HsPragSCC a b c) e)) =
  L l . HsPragE x (HsPragSCC a b c) <$> liftMonadicExpr given tcs e
liftMonadicExpr _ _ e@(L _ (HsBracket _ _)) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Template Haskell and Quotation are not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L _ (HsSpliceE _ _)) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Template Haskell and Quotation are not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L _ HsTcBracketOut {}) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Template Haskell and Quotation are not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L _ HsProc {}) = do
  reportError
    ( mkMsgEnvelope
        (getLocA e)
        neverQualify
        "Arrow notation is not supported by the plugin"
    )
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsStatic x e)) =
  L l . HsStatic x <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsTick a tick e)) = do
  (L l .) . HsTick a <$> liftTick tcs tick <*> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsBinTick a b c e)) =
  L l . HsBinTick a b c <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (XExpr (WrapExpr (HsWrap w e)))) = do
  e' <- unLoc <$> liftMonadicExpr given tcs (L l e)
  w' <- liftWrapperTcM True tcs w
  return (L l (mkHsWrap w' e'))
liftMonadicExpr _ _ (L _ (HsUnboundVar _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsRecFld _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsOverLabel _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsIPVar _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsRnBracketOut _ _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsConLikeOut _ _)) = undefined
liftMonadicExpr _ _ (L _ (XExpr (ExpansionExpr _))) = undefined
liftMonadicExpr _ _ (L _ (HsGetField _ _ _)) = undefined
liftMonadicExpr _ _ (L _ (HsProjection _ _)) = undefined

liftMonadicStmts ::
  HsStmtContext GhcRn ->
  Bool ->
  Type ->
  [Ct] ->
  TyConMap ->
  [ExprLStmt GhcTc] ->
  TcM [ExprLStmt GhcTc]
liftMonadicStmts _ _ _ _ _ [] = return []
liftMonadicStmts ctxt ctxtSwitch ty given tcs (s : ss) = do
  (s', vs) <- liftMonadicStmt s
  ss' <- liftMonadicStmts ctxt ctxtSwitch ty given tcs ss
  if null vs
    then return (s' : ss')
    else do
      e <- shareVars tcs vs given (noLocA (HsDo ty ctxt (noLocA ss'))) ty
      return [s', noLocA (LastStmt noExtField e Nothing NoSyntaxExprTc)]
  where
    liftMonadicStmt ::
      ExprLStmt GhcTc ->
      TcM (ExprLStmt GhcTc, [(Var, LocatedN Var)])
    liftMonadicStmt (L l (LastStmt x e a r)) = do
      e' <- liftMonadicExpr given tcs e
      r' <-
        if synExprExists r
          then trans1 r
          else return r
      return (L l (LastStmt x e' a r'), [])
    liftMonadicStmt (L l (BindStmt (XBindStmtTc b x m f) p e)) = do
      -- p is definitely just a varPat and f is NoSyntaxExprTc or Nothing
      (p', vs) <- liftPattern tcs p
      e' <- liftMonadicExpr given tcs e
      x' <- liftTypeTcM tcs x
      b' <- transBind b
      return (L l (BindStmt (XBindStmtTc b' x' m f) p' e'), vs)
    liftMonadicStmt (L _ ApplicativeStmt {}) = do
      reportError
        ( mkMsgEnvelope
            (getLocA s)
            neverQualify
            "Applicative do-notation is not supported by the plugin"
        )
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l (BodyStmt x e se g)) = do
      x' <- liftTypeTcM tcs x
      e' <- liftMonadicExpr given tcs e
      se' <- trans2 se
      g' <-
        if synExprExists g
          then trans1 g
          else return g
      return (L l (BodyStmt x' e' se' g'), [])
    liftMonadicStmt (L l (LetStmt x bs)) = do
      (bs', vs) <- liftLocalBinds given tcs bs
      return (L l (LetStmt x bs'), vs)
    liftMonadicStmt (L _ ParStmt {}) = do
      reportError
        ( mkMsgEnvelope
            (getLocA s)
            neverQualify
            "Parallel list comprehensions are not supported by the plugin"
        )
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L _ TransStmt {}) = do
      reportError
        ( mkMsgEnvelope
            (getLocA s)
            neverQualify
            "Transformative list comprehensions are not supported by the plugin"
        )
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L _ RecStmt {}) = do
      reportError
        ( mkMsgEnvelope
            (getLocA s)
            neverQualify
            "Recursive do-notation is not supported by the plugin"
        )
      failIfErrsM
      return (s, [])

    synExprExists NoSyntaxExprTc = False
    synExprExists _ = True

    trans1 (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLocA (mkHsWrap w e))
      e1ty <- getTypeOrPanic (noLocA e) >>= liftTypeTcM tcs -- ok
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let (ty1, ty2) = splitMyFunTy ftc mtc (bindingType e1ty)
      e2 <- mkApp (mkNewApply1 (bindingType ty1)) (bindingType ty2) [e1]
      ws' <- mapM (liftWrapperTcM True tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    trans1 NoSyntaxExprTc = return NoSyntaxExprTc

    transBind (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLocA (mkHsWrap w e))
      e1ty <- getTypeOrPanic (noLocA e) >>= liftTypeTcM tcs -- ok
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let (ty1, restty) = splitMyFunTy ftc mtc (bindingType e1ty)
      let (ty2, ty3) = splitMyFunTy ftc mtc (bindingType restty)
      e2 <-
        mkApp
          (mkNewApply2Unlifted (bindingType ty1) (bindingType ty2))
          (bindingType ty3)
          [e1]
      ws' <- mapM (liftWrapperTcM True tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    transBind NoSyntaxExprTc = return NoSyntaxExprTc

    trans2 (SyntaxExprTc e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLocA (mkHsWrap w e))
      e1ty <- getTypeOrPanic (noLocA e) >>= liftTypeTcM tcs -- ok
      mtc <- getMonadTycon
      ftc <- getFunTycon
      let (ty1, restty) = splitMyFunTy ftc mtc (bindingType e1ty)
      let (ty2, ty3) = splitMyFunTy ftc mtc (bindingType restty)
      e2 <-
        mkApp
          (mkNewApply2 (bindingType ty1) (bindingType ty2))
          (bindingType ty3)
          [e1]
      ws' <- mapM (liftWrapperTcM True tcs) ws
      return (SyntaxExprTc (unLoc e2) ws' WpHole)
    trans2 NoSyntaxExprTc = return NoSyntaxExprTc

liftLambda ::
  [Ct] ->
  TyConMap ->
  SrcSpanAnnA ->
  Maybe Type ->
  MatchGroup GhcTc (LHsExpr GhcTc) ->
  TcM (LHsExpr GhcTc)
liftLambda given tcs l _ mg = do
  mg'@(MG (MatchGroupTc [Scaled _ arg] res) _ _) <-
    liftMonadicEquation given tcs mg
  let e = L l (HsLam noExtField mg')
  mkApp mkNewReturnFunTh (arg `mkVisFunTyMany` res) [noLocA (HsPar EpAnnNotUsed e)]

-- We need to pay special attention to a lot of different kinds of variables.
-- Most of those kinds can be treated sinilarly (see below), but for
-- record selectors, we need a different approach.
liftVarWithWrapper ::
  [Ct] ->
  TyConMap ->
  HsWrapper ->
  Var ->
  Unique ->
  TcM (LHsExpr GhcTc)
liftVarWithWrapper given tcs w v dttKey
  | varUnique v == coerceKey,
    ([_, ty1, ty2], _) <- collectTyApps w =
      transCoerce tcs given ty1 ty2
  | varUnique v == tagToEnumKey = do
      let appliedType = head $ fst $ collectTyApps w
      liftedType <- liftTypeTcM tcs appliedType
      -- tagToEnum :: Int# -> tyApp in w
      -- returnFunc (\flint ndint -> ndint >>= \(I# i) -> toFL (tagToEnum @w i)))
      lam <-
        liftQ
          [|
            \ttenum ndint ->
              ndint
                >>= (\(I# i) -> toFL (ttenum i))
            |]
      mtycon <- getMonadTycon
      let argty = mkTyConApp mtycon [intTy]
      let resty = liftedType
      let ety =
            (intPrimTy `mkVisFunTyMany` appliedType)
              `mkVisFunTyMany` argty
              `mkVisFunTyMany` resty
      let tte = noLocA (mkHsWrap w (HsVar noExtField (noLocA v)))
      e <- noLocA . HsPar EpAnnNotUsed <$> mkApp (mkNewAny lam) ety [tte]
      mkApp mkNewReturnFunTh (argty `mkVisFunTyMany` resty) [e]
  | varUnique v == dttKey = do
      let appliedType = head $ fst $ collectTyApps w
      liftedType <- liftTypeTcM tcs appliedType
      -- dataToTagKey :: tyApp in w -> Int#
      -- returnFunc (\x -> x >>= \x' -> return (I# (dataToTagKey @w x')))
      lam <- liftQ [|\dtt x -> x >>= (\x' -> return (I# (dtt x')))|] -- do not use ".", because unlifted
      mtycon <- getMonadTycon
      w' <- liftWrapperTcM True tcs w
      let argty = liftedType
      let resty = mkTyConApp mtycon [intTy]
      let ety =
            (bindingType liftedType `mkVisFunTyMany` intPrimTy)
              `mkVisFunTyMany` argty
              `mkVisFunTyMany` resty
      let dtt = noLocA (mkHsWrap w' (HsVar noExtField (noLocA v)))
      e <- noLocA . HsPar EpAnnNotUsed <$> mkApp (mkNewAny lam) ety [dtt]
      mkApp mkNewReturnFunTh (argty `mkVisFunTyMany` resty) [e]
  | isRecordSelector v = do
      -- lift type
      mtc <- getMonadTycon
      let mty = mkTyConTy mtc
      stc <- getShareClassTycon
      ftc <- getFunTycon
      w' <- liftWrapperTcM True tcs w
      us <- getUniqueSupplyM

      let (apps, abstrs) = collectTyApps w'
      let realApps = drop (length abstrs) apps
      let (arg, res) = splitMyFunTy ftc mtc (instantiateWith realApps (varType v))

      let p = sel_tycon (idDetails v)
      v' <- liftIO (getLiftedRecSel stc ftc mty us tcs p v)

      let vExpr = noLocA (mkHsWrap w' (HsVar noExtField (noLocA v')))
      e <- case p of
        RecSelData tc
          -- translate any newtype  record selector "sel" to "return (fmap sel)"
          | isNewTyCon tc -> mkApp (mkNewFmapTh arg) res [vExpr]
        -- translate any datatype record selector "sel" to "return (>>= sel)"
        _ -> do
          thE <- liftQ [|flip (>>=)|]
          bind <- mkApp (mkNewBindTh arg) (bindingType res) []
          bindTy <- getTypeOrPanic bind
          let thEty = bindTy -- TODO
          mkApp (mkNewAny thE) thEty [bind]
      ety <- getTypeOrPanic e -- ok
      mkApp mkNewReturnTh ety [noLocA (HsPar EpAnnNotUsed e)]
  | otherwise = do
      -- lift type
      w' <- liftWrapperTcM True tcs w
      mtc <- getMonadTycon
      stc <- getShareClassTycon
      us <- getUniqueSupplyM
      ftc <- getFunTycon
      ty' <- liftIO (liftTypeIfRequired stc ftc mtc us tcs (varType v))

      let (apps, absts) = collectTyApps w'
      let abstsWrap = foldr ((<.>) . WpTyLam) WpHole absts

      -- 1. If it is a typeclass operation, we re-create it from scratch to get
      --    the unfolding information right.
      -- 2. If it is a default method,
      --    we have to set the correct type and
      --    switch to the correct default method.
      --    For a non-builtin default method,
      --    we have to make some adjustments to the lifting.
      -- 3. If it is a LclId, just use the lifted type.
      -- 4. If it is one of a specific set of methods from the Prelude
      --    (due to deriving), we have to switch to the correct method.
      --    This falls back to just returning the current identifier,
      --    If no replacement function is found.
      let mv' | ClassOpId cls <- idDetails v = do
                cls' <- liftIO (getLiftedClass cls tcs)
                -- lookup the corresponding new name for the selector
                let sels = map idName (classAllSelIds cls)
                    sels' = map idName (classAllSelIds cls')
                    mdl = moduleName (nameModule (varName v))
                    occ | mdl == mkModuleName "Plugin.BuiltIn"
                                    = occName v
                        | otherwise = removeNameSuffix (occName v)
                Just (_, idx) <- return $ find ((== occ) . occName . fst) (zip sels [0..])
                -- a built-in class already knows its correct index
                -- this differs from our other plugins
                let idx' = idx + if cls' == cls then 0 else length (classTyVars cls)
                return (mkDictSelId (sels' !! idx') cls')
              | isLocalId v =
                return (setVarType v ty')
              | '$':'d':'m':_ <- occNameString (occName v) = do
                -- Split the type to get the class that this is the default method
                -- for, and look up the new version of that class.
                let tc = tyConAppTyCon (funArgTy (snd (splitForAllTyCoVars (varType v))))
                tc' <- liftIO (lookupTyConMap GetNew tcs tc)
                let defMethName = tyConClass_maybe tc' >>= find defLike . classOpItems
                    defLike (_ , Just (n', _)) = isLiftedDefaultName (occName v) (occName n')
                    defLike _                  = False
                case defMethName of
                  Just (_, Just (newnm, _)) -> lookupId newnm
                  _ -> failWithTc (ppr (v, tc'))
              | otherwise = lookupWiredInFunc v ty'
      v' <- mv'

      let monotype = instantiateWith apps (varType v')
          getPred (Anon _ (Scaled _ t))
            | all (\cv -> countVarOcc cv t == 0) absts =
                Just t
          getPred _ = Nothing
          preds = mapMaybe getPred (fst (splitInvisPiTys monotype))

      let isWpHole WpHole = True
          isWpHole _ = False

      if null preds || isWpHole w
        then do
          let newWrap = abstsWrap <.> createWrapperFor (varType v') apps []
          return (noLocA (mkHsWrap newWrap (HsVar noExtField (noLocA v'))))
        else do
          -- construct wanted constraints
          wanted <- newWanteds (OccurrenceOf (varName v')) preds
          let evvars = mapMaybe (getDest . ctev_dest) wanted
              getDest (EvVarDest d) = Just d
              getDest _ = Nothing
              cts = map CNonCanonical wanted

          lvl <- getTcLevel
          env <- getLclEnv
          u <- getUniqueM
          ref1 <- newTcRef emptyEvBindMap
          ref2 <- newTcRef emptyVarSet
          let bindsVar = EvBindsVar u ref1 ref2
          -- filter is just here to be sure
          evidence <-
            if null absts
              then do
                emitConstraints (WC (listToBag cts) emptyBag emptyBag)
                return WpHole
              else do
                let givenVars = map (ctEvEvId . cc_ev) $ filter isGivenCt given
                let i =
                      Implic
                        lvl
                        absts
                        UnkSkol
                        givenVars
                        MaybeGivenEqs
                        False
                        env
                        (WC (listToBag cts) emptyBag emptyBag)
                        bindsVar
                        emptyVarSet
                        emptyVarSet
                        IC_Unsolved
                emitImplication i
                return $ mkWpLet (TcEvBinds bindsVar)

          -- create the new wrapper, with the new dicts and the type applications
          let wdict = createWrapperFor (varType v') apps evvars
          let wall = abstsWrap <.> (evidence <.> wdict)
          return $ noLocA $ mkHsWrap wall $ HsVar noExtField $ noLocA v'

-- (,b,) = return $ \x1 -> return $ \x2 -> return (x1, b, x2)
liftExplicitTuple ::
  [Ct] ->
  TyConMap ->
  [HsTupArg GhcTc] ->
  Boxity ->
  TcM (LHsExpr GhcTc)
liftExplicitTuple given tcs args b = do
  resty <- getTypeOrPanic (noLocA $ ExplicitTuple noExtField args b) -- ok
  lifted <- liftTypeTcM tcs resty
  liftExplicitTuple' (bindingType lifted) [] WpHole args
  where
    liftExplicitTuple' ::
      Type ->
      [LHsExpr GhcTc] ->
      HsWrapper ->
      [HsTupArg GhcTc] ->
      TcM (LHsExpr GhcTc)
    liftExplicitTuple' resty col w (Present _ e : xs) = do
      e' <- liftMonadicExpr given tcs e
      ty <- getTypeOrPanic e >>= liftTypeTcM tcs -- ok
      let w' = WpTyApp (bindingType ty) <.> w
      liftExplicitTuple' resty (e' : col) w' xs
    liftExplicitTuple' resty col w (Missing (Scaled m ty) : xs) = do
      ty' <- liftTypeTcM tcs ty
      v <- noLocA <$> freshVar (Scaled m ty')
      let arg = noLocA (HsVar noExtField v)
      let w' = WpTyApp (bindingType ty') <.> w
      ftc <- getFunTycon
      mtc <- getMonadTycon
      let (_, resty') = splitMyFunTy ftc mtc resty
      inner <- liftExplicitTuple' (bindingType resty') (arg : col) w' xs
      let lam = mkLam v (Scaled m ty') inner resty'
      mkApp mkNewReturnFunTh (ty' `mkVisFunTyMany` resty') [lam]
    liftExplicitTuple' resty col w [] = do
      mTyCon <- getMonadTycon
      let exprArgs = reverse col
      dc <- liftIO (getLiftedCon (tupleDataCon b (length exprArgs)) tcs)
      let ce = mkHsWrap (w <.> WpTyApp (mkTyConTy mTyCon)) (HsConLikeOut noExtField (RealDataCon dc))
      mkApp
        mkNewReturnTh
        resty
        [foldl mkHsApp (noLocA ce) exprArgs]

-- This is for RecordConstructors only.
-- We are interested in lifting the (potential wrapper)
-- and we want to replace the HsConLike with the lifted constructor version.
-- HsConLike is the only sensible option for this PostTcExpr for Haskell2010.
liftConExpr :: TyConMap -> DataCon -> PostTcExpr -> TcM PostTcExpr
liftConExpr tcs dc (XExpr (WrapExpr (HsWrap w _))) = do
  w' <- liftWrapperTcM True tcs w
  return (mkHsWrap w' (HsConLikeOut noExtField (RealDataCon dc)))
liftConExpr _ dc _ = return (HsConLikeOut noExtField (RealDataCon dc))

liftMonadicRecFields ::
  [Ct] ->
  TyConMap ->
  HsRecordBinds GhcTc ->
  TcM (HsRecordBinds GhcTc)
liftMonadicRecFields given tcs (HsRecFields flds dotdot) =
  flip HsRecFields dotdot <$> mapM (liftMonadicRecField given tcs) flds

liftMonadicRecordUpd :: TyConMap -> RecordUpdTc -> TcM RecordUpdTc
liftMonadicRecordUpd tcs (RecordUpdTc cs intys outtys wrap) = do
  RecordUpdTc <$> mapM conLike cs
    <*> mapM (liftInnerTyTcM tcs) intys
    <*> mapM (liftInnerTyTcM tcs) outtys
    <*> liftWrapperTcM True tcs wrap
  where
    conLike (RealDataCon c) = RealDataCon <$> liftIO (getLiftedCon c tcs)
    conLike p@(PatSynCon _) = do
      reportError
        ( mkMsgEnvelope
            noSrcSpan
            neverQualify
            "Pattern synonyms are not supported by the plugin"
        )
      failIfErrsM
      return p

liftMonadicRecordUpdField ::
  [Ct] ->
  TyConMap ->
  LHsRecUpdField GhcTc ->
  TcM (LHsRecUpdField GhcTc)
liftMonadicRecordUpdField given tcs (L l1 (HsRecField x (L l2 ambOcc) e pun)) = do
  ambOcc' <- liftAmbiguousFieldOcc tcs ambOcc
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField x (L l2 ambOcc') e' pun))

liftMonadicRecordProjField ::
  [Ct] ->
  TyConMap ->
  LHsRecUpdProj GhcTc ->
  TcM (LHsRecUpdProj GhcTc)
liftMonadicRecordProjField given tcs (L l1 (HsRecField x lbls e pun)) = do
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField x lbls e' pun))

liftMonadicRecField ::
  [Ct] ->
  TyConMap ->
  LHsRecField GhcTc (LHsExpr GhcTc) ->
  TcM (LHsRecField GhcTc (LHsExpr GhcTc))
liftMonadicRecField given tcs (L l1 (HsRecField x (L l2 occ) e pun)) = do
  occ' <- liftFieldOcc tcs occ
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField x (L l2 occ') e' pun))

-- for some weird reason, the "v" is not a selector function.
-- (It should be according to the doumentation)
-- By looking it up in the type environment again, we fix this.
liftFieldOcc :: TyConMap -> FieldOcc GhcTc -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs (FieldOcc v _) = do
  tenv <- tcg_type_env <$> getGblEnv
  case lookupTypeEnv tenv (varName v) of
    Just (AnId realV)
      | RecSelId parent _ <- idDetails realV ->
          do
            mty <- mkTyConTy <$> getMonadTycon
            stc <- getShareClassTycon
            ftc <- getFunTycon
            us <- getUniqueSupplyM
            v' <- liftIO (getLiftedRecSel stc ftc mty us tcs parent v)
            return (FieldOcc v' (noLocA (nameRdrName (varName v'))))
    _ -> panicBndr "Expected RecSel in FieldOcc of Record operation" v

liftAmbiguousFieldOcc ::
  TyConMap ->
  AmbiguousFieldOcc GhcTc ->
  TcM (AmbiguousFieldOcc GhcTc)
liftAmbiguousFieldOcc tcs (Unambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs (FieldOcc v n)
  return (Unambiguous v' n')
liftAmbiguousFieldOcc tcs (Ambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs (FieldOcc v n)
  return (Ambiguous v' n')

liftTick :: TyConMap -> CoreTickish -> TcM CoreTickish
liftTick tcs (Breakpoint x i ids) = Breakpoint x i <$> mapM transId ids
  where
    transId v = setVarType v <$> liftTypeTcM tcs (varType v)
liftTick _ t = return t

shareVars ::
  TyConMap ->
  [(Var, LocatedN Var)] ->
  [Ct] ->
  LHsExpr GhcTc ->
  Type ->
  TcM (LHsExpr GhcTc)
shareVars _ vs evs e' ety = do
  foldM (shareVar ety) e' $
    reverse $
      map (second unLoc) $
        sortBy ((. snd) . cmpLocated . snd) vs
  where
    -- share v1 >>= \v2 -> e
    -- differs from the normal lifting, because we optimize for call-by-need
    shareVar ty e (v1, v2)
      | isForAllTy (varType v1) ||
        maxUsage v2 e <= 1 = return (substitute v1 v2 e)
      | Many <- varMult v2 = do
          let v1e = noLocA (HsVar noExtField (noLocA v1))
          let v1ty = varType v1
          s <-
            noLocA . HsPar EpAnnNotUsed
              <$> mkAppWith mkNewShareTh evs v1ty [v1e]
          mtycon <- getMonadTycon
          let sty = mkTyConApp mtycon [v1ty]
          let v2ty = Scaled (varMult v2) (varType v2)
          let l = noLocA (HsPar EpAnnNotUsed (mkLam (noLocA v2) v2ty e ty))
          mkBind evs s sty l ty
      -- Interestingly, we know that v1 and v2 do not ocurr more than once in e,
      -- as long as their multiplicity is not Many. Even if the multiplicity
      -- is polymorphic we know this, as the function could not have
      -- such a multiplicity if the function could not be linear in v1/v2.
      | otherwise = return (substitute v1 v2 e)

maxUsage :: Var -> LHsExpr GhcTc -> Int
maxUsage v = goL
 where
  goL :: LHsExpr GhcTc -> Int
  goL (L _ e) = go e
  go :: HsExpr GhcTc -> Int
  go e' = case e' of
    HsVar _ (L _ v') -> if v == v' then 1 else 0
    XExpr (WrapExpr (HsWrap _ e)) -> go e
    HsLam _ mg -> goMG mg * 2 -- a variable ocurring in a lambda might be used more than once.
    HsLamCase _ mg -> goMG mg * 2
    OpApp _ e1 op e2 -> goL e1 + goL op + goL e2
    HsApp _ fn ex -> goL fn + goL ex
    HsAppType _ e _ -> goL e
    NegApp _ e (SyntaxExprTc n _ _) -> goL e + go n
    HsPar _ e -> goL e
    ExplicitTuple _ args _ -> sum (map goTup args)
    ExplicitSum _ _ _ e -> goL e
    HsCase _ scr br -> goL scr + goMG br
    HsIf _ e1 e2 e3 -> goL e1 + max (goL e2) (goL e3)
    HsLet _ bs e -> goBs bs + goL e
    HsDo _ _ (L _ stmts) -> sum (map goStmt stmts)
    ExplicitList _ es -> sum (map goL es)
    RecordUpd _ e fs -> goL e + goF fs
    ExprWithTySig _ e _ -> goL e
    ArithSeq _ (Just (SyntaxExprTc e _ _)) i -> go e + sum (map goL (arithSeqArgs i))
    ArithSeq _ _ i -> sum (map goL (arithSeqArgs i))
    HsPragE _ _ e -> goL e
    HsTick _ _ e -> goL e
    HsBinTick _ _ _ e -> goL e
    _                 -> 0

  goMG (MG _ (L _ ms) _) = maximum (map goM ms)
  goM :: LMatch GhcTc (LHsExpr GhcTc) -> Int
  goM (L _ (Match _ _ _ (GRHSs _ [L _ (GRHS _ _ e)] _))) = goL e
  goM _                                                  = 0
  goTup (Present _ e) = goL e
  goTup _             = 0
  goBs _ = 2 -- TODO, also remember that functions probably use it more than once
  goStmt _ = 2 -- TODO
  goF _ = 2 -- TODO

substitute :: Data a => Var -> Var -> a -> a
substitute new old = everywhere (mkT substVar)
  where
    u = varName old
    substVar v = if varName v == u then new else v

{- HLINT ignore "Reduce duplication" -}
