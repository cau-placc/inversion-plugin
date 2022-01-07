{-# LANGUAGE MagicHash         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-|
Module      : Plugin.Trans.Expr
Description : Main lifting transformation for functions and expressions
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module provides the main transformation of our monadic lifting for
functions and expressions to integrate our effect.
-}
module Plugin.Trans.Expr (liftMonadicBinding) where

import Control.Applicative
import Control.Monad

import Data.Char (isAlpha)
import Data.Data (Data)
import Data.List
import Data.Tuple.Extra
import Data.Maybe
import Data.Generics.Aliases
import Data.Generics.Schemes

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Lit
import GHC.Hs.Types
import GHC.Hs.Expr
import GHC.Hs.Utils
import GHC.Int
import TysPrim
import PrimOp
import SrcLoc
import ConLike
import GhcPlugins
import Bag
import TyCoRep
import TcType
import TcEvidence
import TcOrigin
import TcSimplify
import TcMType
import TcRnMonad
import TcHsSyn
import InstEnv
import Constraint
import Class
import MkId
import ErrUtils
import IfaceEnv
import Finder
import PrelNames

import Plugin.Trans.Constr
import Plugin.Trans.Record
import Plugin.Trans.Type
import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Trans.Pat
import Plugin.Trans.Class
import Plugin.Trans.FunWiredIn
import Plugin.Trans.Coerce
import Plugin.Trans.CreateSyntax
import Plugin.Trans.DictInstFun
import Plugin.Effect.Monad
import Plugin.Effect.Util

-- | Transform the given binding with a monadic lifting to incorporate
-- our nondeterminism as an effect.
-- This function also transforms any nested bindings recursively and
-- thus needs to know whether it is a local binding or not.
-- First  Bool: This is a local binding, swap the Unique for sharing purposes
-- Second Bool: This is a nested AbsBinds, do not insert into type env
liftMonadicBinding :: Bool -> Bool -> [Ct] -> TyConMap -> [(ClsInst, ClsInst)]
                   -> HsBindLR GhcTc GhcTc
                   -> TcM ([HsBindLR GhcTc GhcTc], [(Var,Var)])
liftMonadicBinding _ _ given tcs _ (FunBind a (L b name) eqs c ticks) = do
  eqs' <- liftMonadicEquation given tcs eqs
  ty <- liftTypeTcM tcs (varType name)
  ticks' <- mapM (liftTick tcs) ticks
  let name' = setVarType name ty
  return ([FunBind a (L b name') eqs' c ticks'], [])
liftMonadicBinding lcl _ given tcs _ (AbsBinds a b c d e f g)
  -- we do not want to lift dicts or record selectors or other system stuff here
  | all (noSystemNameOrRec . abe_poly) d = do
  -- create the dictionary variables
  lclEnv <- getLclEnv
  let ctloc = mkGivenLoc topTcLevel UnkSkol lclEnv

  allEvs <- liftIO (mapM replaceEv c)
  let cts = mkGivens ctloc allEvs
  let given' = given ++ cts


  (d', vs) <- unzip <$> mapM liftEx d
  let vs' = catMaybes vs

  -- lift inner bindings
  let bs = map unLoc (bagToList f)
  f' <- listToBag . map noLoc . concat
          <$> mapM (fmap fst . liftMonadicBinding False True given' tcs [])
              (foldr (uncurry substitute) bs vs')

  e' <- mapM (liftEvidence given' tcs) (filter isExportedEv (concatMap flattenEv e))
  return ([AbsBinds a b allEvs d' e' f' g], vs')
  where
    replaceEv ev = setVarType ev <$> replaceTyconTy tcs (varType ev)

    -- Basically do the same as in liftTopTypes, but this time for
    -- both the poly and mono type and for local bindings as well
    liftEx :: ABExport GhcTc -> TcM (ABExport GhcTc, Maybe (Var,Var))
    liftEx (ABE x v1 v2 w p) = do
      -- change unique only for local decls, as only those are shared
      let u = varUnique v1

      env <- getGblEnv
      let tenvvar = tcg_type_env_var env


      -- lift types
      mtycon <- getMonadTycon
      ftc <- getFunTycon
      us2 <- getUniqueSupplyM

      -- We only want to introduce Shareable constraints for the type
      -- variables bound in this AbsBind, so we manually split off
      -- all type and evidence abstractions bound here.
      -- Then we can do the lifting and stuff.
      -- All of this is only done, when a lifting is even required.
      let v1ty = varType v1
      ty1 <- case splitTyConApp_maybe (snd (splitPiTysInvisible v1ty)) of
        Just (tc, _) | tc == mtycon
          -> liftIO (replaceTyconTy tcs v1ty)
        _ -> do
          let (bs1, t1) = splitPiTysInvisibleN (length b + length c) v1ty
          let cons = []
          bs1' <- mapM (replacePiTyTcM tcs) bs1
          mkPiTys bs1' . flip (foldr mkInvisFunTy) cons
            <$> liftTypeTcM tcs t1

      let (vs, rest) = collectHsWrapBinders w
          vswrap = foldr ((<.>) . WpTyLam) WpHole vs

      -- lift the mono type and create the new variables.
      ty2 <- liftIO (liftTypeIfRequired ftc mtycon us2 tcs (varType v2))
      let v2' = setVarType v2 ty2
      let v1' = setVarType v1 ty1
      -- also (possibly) change unique for sharing
      let v1u = setVarUnique v1' u

      tenv <- readTcRef tenvvar
      unless lcl $ writeTcRef tenvvar (tenv `extendTypeEnv` AnId v1u)

      return (ABE x v1u v2' (vswrap <.> rest) p, Nothing)
    liftEx ex = return (ex, Nothing)

    -- Do not lift any system stuff, except instance fun definitions ($c),
    -- class default methods ($dm) and enumeration tag-system stuff.
    noSystemNameOrRec v = case occNameString (occName v) of
      n | "$con2tag_" `isPrefixOf` n -> True
        | "$maxtag"   `isPrefixOf` n -> True
        | "$tag2con"  `isPrefixOf` n -> True
      '$':'c':_                      -> True
      '$':'d':'m':_                  -> True
      '$':xs@(_:_) | any isAlpha xs  -> False
      _             -> not (isRecordSelector v)

    flattenEv (TcEvBinds _) = []
    flattenEv (EvBinds ebs) = bagToList ebs
    isExportedEv (EvBind v _ _) = any ((==v) . abe_mono) d
liftMonadicBinding _ _ _ tcs clsInsts bind@(AbsBinds _ _ _ d _ _ _)
  | all (isDictFun . abe_poly) d =
    maybe ([bind], []) ((,[]) . (:[]))
      <$> liftDictInstFun bind tcs clsInsts
  where
    isDictFun v = case occNameString (occName v) of
      '$':'f':_ -> True
      _         -> False
liftMonadicBinding _ _ _ tcs _ bind@(AbsBinds _ _ _ d _ _ _)
  | all (isRecordSelector . abe_poly) d = do
    r <- liftRecordSel tcs bind
    case r of
      Just b  -> return ([b], [])
      Nothing -> return ([], [])
liftMonadicBinding _ _ _ tcs _ (VarBind x1 name _ inl)
  -- This is the error binding for an unimplemented type class function.
  -- Anything like $c... = noMethodBindingError @ 'LiftedRep @ ty "..."#,
  | '$':'c':_ <- occNameString (occName name) = do
    f <- liftQ [| Control.Applicative.empty |]
    ty <- liftTypeTcM tcs (varType name)
    e <- mkApp (mkNewAny f) ty []
    return ([VarBind x1 (setVarType name ty) e inl], [])
liftMonadicBinding _ _ _ _ _ a = return ([a], [])

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
  EvBinds <$> simplifyTop (WC (listToBag (cts ++ given)) emptyBag)

liftLocalBinds :: [Ct] -> TyConMap -> LHsLocalBinds GhcTc
               -> TcM (LHsLocalBinds GhcTc, [(Var,Var)])
liftLocalBinds given tcs (L l (HsValBinds x b)) = do
  (b', vs) <- liftValBinds given tcs b
  return (L l (HsValBinds x b'), vs)
liftLocalBinds _ _ b@(L l (HsIPBinds _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return (b, [])
liftLocalBinds _ _ b = return (b, [])

liftValBinds :: [Ct] -> TyConMap -> HsValBindsLR GhcTc GhcTc
             -> TcM (HsValBindsLR GhcTc GhcTc, [(Var,Var)])
liftValBinds _ _ bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
liftValBinds given tcs (XValBindsLR (NValBinds bs _)) = do
  (bs', vss) <- unzip <$> mapM liftNV bs
  return (XValBindsLR (NValBinds bs' []), concat vss)
  where
    liftNV :: (RecFlag, LHsBinds GhcTc)
           -> TcM ((RecFlag, LHsBinds GhcTc), [(Var,Var)])
    liftNV (rf, b) = do
      let bs1 = map unLoc (bagToList b)
      (bs2, vss) <- first (map noLoc . concat) . unzip <$>
        mapM (liftMonadicBinding True False given tcs []) bs1
      return ((rf, listToBag bs2), concat vss)

liftMonadicEquation :: [Ct] -> TyConMap
                    -> MatchGroup GhcTc (LHsExpr GhcTc)
                    -> TcM (MatchGroup GhcTc (LHsExpr GhcTc))
liftMonadicEquation given tcs (MG a (L b alts) c) = do
  alts' <- mapM (liftMonadicAlt given tcs) alts
  a' <- liftMGTc tcs a
  return (MG a' (L b alts') c)
liftMonadicEquation _ _ a = return a

liftMGTc :: TyConMap -> MatchGroupTc -> TcM MatchGroupTc
liftMGTc tcs (MatchGroupTc args res) = do
  res' <- liftTypeTcM tcs res
  args' <- mapM (liftTypeTcM tcs) args
  return (MatchGroupTc args' res')

liftMonadicAlt :: [Ct] -> TyConMap
               -> LMatch GhcTc (LHsExpr GhcTc)
               -> TcM (LMatch GhcTc (LHsExpr GhcTc))
liftMonadicAlt given tcs (L a (Match b c d rhs)) = do
  (d', s) <- unzip <$> mapM (liftPattern tcs) d
  rhs' <- liftMonadicRhs (concat s) given tcs rhs
  return (L a (Match b c d' rhs'))
liftMonadicAlt _ _ a = return a

liftMonadicRhs :: [(Var, Var)] -> [Ct] -> TyConMap
               -> GRHSs GhcTc (LHsExpr GhcTc)
               -> TcM (GRHSs GhcTc (LHsExpr GhcTc))
liftMonadicRhs s given tcs (GRHSs a grhs b) = do
  grhs' <- mapM (liftMonadicGRhs s given tcs) grhs
  return (GRHSs a grhs' b)
liftMonadicRhs _ _ _ a = return a

liftMonadicGRhs :: [(Var, Var)] -> [Ct] -> TyConMap
                -> LGRHS GhcTc (LHsExpr GhcTc)
                -> TcM (LGRHS GhcTc (LHsExpr GhcTc))
liftMonadicGRhs s given tcs (L a (GRHS b c body)) = do
  body' <- liftMonadicExpr given tcs body
  L a . GRHS b c <$> shareVars s body'
liftMonadicGRhs _ _ _ a = return a

liftMonadicExpr :: [Ct] -> TyConMap -> LHsExpr GhcTc
                -> TcM (LHsExpr GhcTc)
liftMonadicExpr given tcs (L _ (HsVar _ (L _ v))) =
  liftVarWithWrapper given tcs WpHole v
liftMonadicExpr given tcs (L _ (HsWrap _ w (HsVar _ (L _ v)))) =
  liftVarWithWrapper given tcs w v
liftMonadicExpr _    _    e@(L _ (HsLit _ (HsIntPrim _ _))) = do
  hscEnv <- getTopEnv
  Found _ mdl <- liftIO $
    findImportedModule hscEnv (mkModuleName "GHC.Int") Nothing
  i64tycon <- lookupOrig mdl ( mkTcOcc "Int64" ) >>= lookupTyCon
  conE <- liftQ [| I64# |]
  let conty = mkVisFunTy intPrimTy (mkTyConTy i64tycon)
  lit <- mkApp (mkNewAny conE) conty [e]
  let retty = mkTyConTy i64tycon
  mkApp mkNewReturnTh retty [noLoc (HsPar noExtField lit)]
liftMonadicExpr _    tcs e@(L _ HsLit{}) = do
  ty <- getTypeOrPanic e
  ty' <- liftInnerTyTcM tcs ty
  res <- mkApp (mkNewToFL ty) ty' [e]
  return $ noLoc $ HsPar noExtField res
liftMonadicExpr given tcs (L l (HsOverLit _ lit)) =
  case ol_witness lit of
    -- if this is geniunely a Double or Float, just wrap it with toFL
    e@(HsApp _ (L _ (HsConLikeOut _ (RealDataCon dc))) _)
      | dc == doubleDataCon || dc == floatDataCon -> do
        ty <- getTypeOrPanic (noLoc e)
        ty' <- liftInnerTyTcM tcs ty
        mkApp (mkNewToFL ty) ty' [noLoc e]
    -- otherwise, just lift the witness
    e -> liftMonadicExpr given tcs (L l e)
liftMonadicExpr given tcs (L l (HsLam x mg)) = do
  mg'@(MG (MatchGroupTc [arg] res) _ _) <- liftMonadicEquation given tcs mg
  let e = L l (HsLam x mg')
  let ty = mkVisFunTy arg res
  mkApp mkNewReturnFunTh ty [noLoc (HsPar noExtField e)]
liftMonadicExpr given tcs (L l (HsLamCase x mg)) = do
  mg'@(MG (MatchGroupTc [arg] res) _ _) <- liftMonadicEquation given tcs mg
  let e = L l (HsLamCase x mg')
  let ty = mkVisFunTy arg res
  mkApp mkNewReturnFunTh ty [noLoc (HsPar noExtField e)]
liftMonadicExpr _ tcs (L _ (HsConLikeOut _ (RealDataCon c)))
  | c == intDataCon = do
    idExp <- liftQ [| returnFLF id |]
    mtycon <- getMonadTycon
    ftycon <- getFunTycon
    hscEnv <- getTopEnv
    Found _ mdl <- liftIO $
      findImportedModule hscEnv (mkModuleName "GHC.Int") Nothing
    i64tycon <- lookupOrig mdl ( mkTcOcc "Int64" ) >>= lookupTyCon
    let ty = mkTyConApp mtycon [mkTyConApp ftycon [mkTyConTy i64tycon, mkTyConTy i64tycon]]
    mkApp (mkNewAny idExp) ty []
  | otherwise = do
    c' <- liftIO (getLiftedCon c tcs)
    let tys = dataConOrigArgTys c'
    e <- fst <$> mkConLam Nothing c' tys []
    return $ noLoc $ HsPar noExtField e
liftMonadicExpr _ tcs (L _ (HsWrap _ w (HsConLikeOut _ (RealDataCon c)))) = do
  c' <- liftIO (getLiftedCon c tcs)
  w' <- liftWrapperTcM tcs w
  let apps = collectTyApps w'
  mty <- mkTyConTy <$> getMonadTycon
  let tys = conLikeInstOrigArgTys (RealDataCon c') (mty : apps)
  e <- fst <$> mkConLam (Just w') c' tys []
  return $ noLoc $ HsPar noExtField e
liftMonadicExpr given tcs (L _ (OpApp _ e1 op e2)) = do
  -- e1 `op` e2
  -- -> (op `appFL` e1) `appFL` e2
  e1' <- liftMonadicExpr given tcs e1
  op' <- liftMonadicExpr given tcs op
  e2' <- liftMonadicExpr given tcs e2
  opty1 <- getTypeOrPanic op'
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let (argty1, opty2) = splitMyFunTy ftc mtc $ bindingType opty1
  let (argty2, _    ) = splitMyFunTy ftc mtc $ bindingType opty2
  e1'' <- mkAppFL given op' opty1 e1' argty1
  let bracketed = noLoc (HsPar noExtField e1'')
  e2'' <- mkAppFL given bracketed opty2 e2' argty2
  return $ noLoc $ HsPar noExtField e2''
liftMonadicExpr given tcs (L _ (HsApp _ fn ex)) = do
  -- e1 e2
  -- -> e1 `appFL` e2
  fn' <- liftMonadicExpr given tcs fn
  funty' <- getTypeOrPanic fn
  funty <- liftTypeTcM tcs funty'
  ex' <- liftMonadicExpr given tcs ex
  ftc <- getFunTycon
  mtc <- getMonadTycon
  let (argty, _) = splitMyFunTy ftc mtc $ bindingType funty
  res <- mkAppFL given fn' funty ex' argty
  return $ noLoc $ HsPar noExtField res
liftMonadicExpr given tcs (L _ (HsAppType _ e _)) =
  liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (NegApp _ e (SyntaxExpr n ws w))) =
  liftMonadicExpr given tcs (L l (HsWrap noExtField w
    (HsApp noExtField (noLoc n)
                 (fmap (HsWrap noExtField (head ws)) e))))
liftMonadicExpr given tcs (L l (HsPar x e)) =
  L l . HsPar x <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (SectionL _ e1 e2)) =
  liftMonadicExpr given tcs (L l (HsApp noExtField e2 e1))
liftMonadicExpr given tcs (L _ (SectionR _ e1 e2)) = do
  -- (`e1` e2)
  -- \(v :: arg1) -> (e1 v) e2 :: res
  ty <- getTypeOrPanic e1
  let (arg1, ty') = splitFunTy ty
  let (_   , res) = splitFunTy ty'
  v <- noLoc <$> freshVar arg1
  liftMonadicExpr given tcs
    (mkLam v arg1 (mkHsApp (mkHsApp e1 (noLoc (HsVar noExtField v))) e2) res)
liftMonadicExpr given tcs (L _ (ExplicitTuple _ args b)) =
  liftExplicitTuple given tcs args b
liftMonadicExpr _    _   e@(L l ExplicitSum {}) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsCase _ scr br)) = do
  br'@(MG (MatchGroupTc _ ty2) _ _) <- liftMonadicEquation given tcs br
  scr' <- liftMonadicExpr given tcs scr
  ty1 <- getTypeOrPanic scr'
  mkBind given scr' ty1 (noLoc $ HsPar noExtField $ L l $ HsLamCase noExtField br') ty2
liftMonadicExpr given tcs (L l (HsIf _ Nothing e1 e2 e3)) = do
  -- if e1 then e2 else e3
  -- -> e1 >>= \case { True -> e1; _ -> e2 }
  e1' <- liftMonadicExpr given tcs e1
  e2' <- liftMonadicExpr given tcs e2
  e3' <- liftMonadicExpr given tcs e3
  ty1' <- getTypeOrPanic e1'
  ty2' <- getTypeOrPanic e2'
  let ty1 = bindingType ty1'
  v <- noLoc <$> freshVar ty1
  let ife = HsIf noExtField Nothing (noLoc (HsVar noExtField v)) e2' e3'
  let alt = mkSimpleAlt LambdaExpr (noLoc ife) [noLoc (VarPat noExtField v)]
  let mgtc = MatchGroupTc [ty1] ty2'
  let mg = MG mgtc (noLoc [noLoc alt]) Generated
  mkBind given e1' ty1' (noLoc $ HsPar noExtField $ L l $ HsLam noExtField mg) ty2'
liftMonadicExpr given tcs (L l (HsIf _ (Just se) e1 e2 e3)) = do
  let args = zipWith (mapLoc . HsWrap noExtField)
        (syn_arg_wraps se) [e1, e2, e3]
  liftMonadicExpr given tcs (L l (HsWrap noExtField (syn_res_wrap se)
    (unLoc (foldl1 mkHsApp (noLoc (syn_expr se) : args)))))
liftMonadicExpr _ _ e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
liftMonadicExpr given tcs (L l (HsLet x bs e)) = do
  -- Lift local binds first, so that they end up in the type environment.
  (bs', vs) <- liftLocalBinds given tcs bs
  e' <- liftMonadicExpr given tcs e
  e'' <- shareVars vs e'
  return (L l (HsLet x bs' e''))
liftMonadicExpr given tcs (L l1 (HsDo x ctxt (L l2 stmts))) = do
  x' <- liftTypeTcM tcs x
  -- Because ListComp are not overloadable,
  -- we have to change them to MonadComp.
  let ctxtSwitch | ListComp <- ctxt = True
                 | otherwise        = False
  let ctxt' | ctxtSwitch = MonadComp
            | otherwise  = ctxt
  stmts' <- liftMonadicStmts ctxt' ctxtSwitch x' given tcs stmts
  return (L l1 (HsDo x' ctxt' (L l2 stmts')))
liftMonadicExpr given tcs (L _ (ExplicitList ty Nothing es)) = do
  -- [e1, ..., en]
  -- -> return (Cons e1 (return (Cons ... (return (Cons en (return Nil))))))
  elemTy <- bindingType <$> liftTypeIfRequiredTcM tcs ty
  em <- mkEmptyList elemTy tcs
  liftedTy <- getTypeOrPanic em
  nil <- mkApp mkNewReturnTh liftedTy [em]
  if null es
    then return nil
    else do
      es' <- mapM (liftMonadicExpr given tcs) es
      cons <- mkConsList elemTy tcs
      let mkCons e1 e2 = let e' = mkHsApp (mkHsApp cons e1) e2
                         in mkApp mkNewReturnTh liftedTy [e']
      foldrM mkCons nil es'
liftMonadicExpr _ _ e@(L l (ExplicitList _ (Just _) _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs
  (L l1 (RecordCon (RecordConTc (RealDataCon c) ce) (L l2 _) fs)) = do
    c' <- liftIO (getLiftedCon c tcs)
    let cn' = dataConWorkId c'
    ce' <- liftConExpr tcs c' ce
    fs' <- liftMonadicRecFields given tcs fs
    let e = L l1 (RecordCon (RecordConTc (RealDataCon c') ce') (L l2 cn') fs')
    if isNewTyCon (dataConTyCon c')
      then return e
      else getTypeOrPanic e >>= flip (mkApp mkNewReturnTh) [e]
liftMonadicExpr _ _ e@(L l (RecordCon (RecordConTc (PatSynCon _) _) _ _)) = do
    flags <- getDynFlags
    reportError (mkErrMsg flags l neverQualify
      "Pattern synonyms are not supported by the plugin")
    failIfErrsM
    return e
liftMonadicExpr given tcs (L l (RecordUpd rtc e fs)) = do
  rtc'@(RecordUpdTc (c:_) inty outty _)  <- liftMonadicRecordUpd tcs rtc
  e' <- liftMonadicExpr given tcs e
  fs' <- mapM (liftMonadicRecordUpdField given tcs) fs
  let vty = conLikeResTy c inty
  v <- noLoc <$> freshVar vty
  let upd = L l (RecordUpd rtc' (noLoc (HsVar noExtField v)) fs')
  let updTy = conLikeResTy c outty
  let updLam = mkLam v vty upd updTy
  mkApp (mkNewFmapTh vty) updTy [updLam, e']
liftMonadicExpr given tcs (L _ (ExprWithTySig _ e _)) =
  liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L _ (ArithSeq x Nothing i)) =
  liftMonadicExpr given tcs (foldl mkHsApp (noLoc x) (arithSeqArgs i))
liftMonadicExpr _ _ e@(L l (ArithSeq _ (Just _) _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsSCC a b c e)) =
  L l . HsSCC a b c <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsCoreAnn a b c e)) =
  L l . HsCoreAnn a b c <$> liftMonadicExpr given tcs e
liftMonadicExpr _ _ e@(L l (HsBracket _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L l (HsSpliceE _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L l HsTcBracketOut {}) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr _ _ e@(L l HsProc {}) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Arrow notation is not supported by the plugin")
  failIfErrsM
  return e
liftMonadicExpr given tcs (L l (HsStatic x e)) =
  L l . HsStatic x <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsTick a tick e)) =
  (L l .) . HsTick a <$> liftTick tcs tick <*> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsBinTick a b c e)) =
  L l . HsBinTick a b c <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsTickPragma a b c d e)) =
  L l . HsTickPragma a b c d <$> liftMonadicExpr given tcs e
liftMonadicExpr given tcs (L l (HsWrap x w e)) = do
  e' <- unLoc <$> liftMonadicExpr given tcs (L l e)
  w' <- liftWrapperTcM tcs w
  return (L l (HsWrap x w' e'))
liftMonadicExpr _ _ e = panicAny "This expression should not occur after TC" e

liftMonadicStmts :: HsStmtContext Name -> Bool -> Type -> [Ct] -> TyConMap
                 -> [ExprLStmt GhcTc] -> TcM [ExprLStmt GhcTc]
liftMonadicStmts _ _ _ _ _ [] = return []
liftMonadicStmts ctxt ctxtSwitch ty given tcs (s:ss) = do
  (s', vs) <- liftMonadicStmt s
  ss' <- liftMonadicStmts ctxt ctxtSwitch ty given tcs ss
  if null vs
    then return (s':ss')
    else do
      e <- shareVars vs (noLoc (HsDo ty ctxt (noLoc ss')))
      return [s', noLoc (LastStmt noExtField e False noSyntaxExpr)]
  where
    liftMonadicStmt :: ExprLStmt GhcTc -> TcM (ExprLStmt GhcTc, [(Var, Var)])
    liftMonadicStmt (L l (LastStmt x e a r)) = do
      e' <- liftMonadicExpr given tcs e
      r' <- if synExprExists r
              then trans1 r
              else return r
      return (L l (LastStmt x e' a r'), [])
    liftMonadicStmt (L l (BindStmt x p e b f)) = do
      -- p is definitely just a varPat and f is noSyntaxExpr
      (p', vs) <- liftPattern tcs p
      e' <- liftMonadicExpr given tcs e
      x' <- liftTypeTcM tcs x
      b' <- transBind b
      return (L l (BindStmt x' p' e' b' f), vs)
    liftMonadicStmt (L l ApplicativeStmt {}) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Applicative do-notation is not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l (BodyStmt x e se g)) = do
      x' <- liftTypeTcM tcs x
      e' <- liftMonadicExpr given tcs e
      se' <- trans2 se
      g' <- if synExprExists g
              then trans1 g
              else return g
      return (L l (BodyStmt x' e' se' g'), [])
    liftMonadicStmt (L l (LetStmt x bs)) = do
      (bs', vs) <- liftLocalBinds given tcs bs
      return (L l (LetStmt x bs'), vs)
    liftMonadicStmt (L l ParStmt {}) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l TransStmt {}) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L l RecStmt {}) =  do
      flags <- getDynFlags
      reportError (mkErrMsg flags l neverQualify
        "Recursive do-notation is not supported by the plugin")
      failIfErrsM
      return (s, [])
    liftMonadicStmt (L _ (XStmtLR _)) = return (s, [])

    synExprExists se | HsLit _ _ <- syn_expr se = False
                     | otherwise                = True

    trans1 (SyntaxExpr e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLoc (HsWrap noExtField w e))
      e1ty <- getTypeOrPanic e1
      let (ty1, ty2) = both bindingType (splitFunTy (bindingType e1ty))
      e2 <- mkApp (mkNewApply1 ty1) ty2 [e1]
      ws' <- mapM (liftWrapperTcM tcs) ws
      return (SyntaxExpr (unLoc e2) ws' WpHole)

    transBind (SyntaxExpr e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLoc (HsWrap noExtField w e))
      e1ty <- getTypeOrPanic e1
      let (ty1, restty) = both bindingType (splitFunTy (bindingType e1ty))
      let (ty2, ty3)  = both bindingType (splitFunTy restty)
      e2 <- mkApp (mkNewApply2Unlifted ty1 ty2) ty3 [e1]
      ws' <- mapM (liftWrapperTcM tcs) ws
      return (SyntaxExpr (unLoc e2) ws' WpHole)

    trans2 (SyntaxExpr e ws w) = do
      e1 <- liftMonadicExpr given tcs (noLoc (HsWrap noExtField w e))
      e1ty <- getTypeOrPanic e1
      let (ty1, restty) = both bindingType (splitFunTy (bindingType e1ty))
      let (ty2, ty3)  = both bindingType (splitFunTy restty)
      e2 <- mkApp (mkNewApply2 ty1 ty2) ty3 [e1]
      ws' <- mapM (liftWrapperTcM tcs) ws
      return (SyntaxExpr (unLoc e2) ws' WpHole)

-- We need to pay special attention to a lot of different kinds of variables.
-- Most of those kinds can be treated sinilarly (see below), but for
-- record selectors, we need a different approach.
liftVarWithWrapper :: [Ct] -> TyConMap -> HsWrapper -> Var
                   -> TcM (LHsExpr GhcTc)
liftVarWithWrapper given tcs w v
  | varUnique v == coerceKey,
    [_,ty1,ty2] <- collectTyApps w = transCoerce tcs given ty1 ty2
  | varUnique v == tagToEnumKey = do
    let appliedType = head $ collectTyApps w
    liftedType <- liftTypeTcM tcs appliedType
    --  tagToEnum :: Int# -> tyApp in w
    -- returnFLF (\flint -> flint >>= \(I64# i) -> toFL (tagToEnum @w i))
    lam <- liftQ [| \ttenum -> returnFLF (\flint -> (>>=) flint (\(I64# i) -> toFL (ttenum i))) |]
    mtycon <- getMonadTycon
    ftycon <- getFunTycon
    hscEnv <- getTopEnv
    Found _ mdl <- liftIO $
      findImportedModule hscEnv (mkModuleName "GHC.Int") Nothing
    i64tycon <- lookupOrig mdl ( mkTcOcc "Int64" ) >>= lookupTyCon
    let int64ty = mkTyConTy i64tycon
    let ty = (intPrimTy `mkVisFunTy` appliedType) `mkVisFunTy` mkTyConApp mtycon [mkTyConApp ftycon [int64ty, bindingType liftedType]]
    noLoc . HsPar noExtField <$> mkApp (mkNewAny lam) ty [noLoc (HsWrap noExtField w (HsVar noExtField (noLoc v)))]
  | isRecordSelector v = do
    -- lift type
    mty <- mkTyConTy <$> getMonadTycon
    ftc <- getFunTycon
    w' <- liftWrapperTcM tcs w
    us <- getUniqueSupplyM

    let apps = collectTyApps w'
    let (arg, res) = splitFunTy (instantiateWith apps (varType v))

    let p = sel_tycon (idDetails v)
    v' <- liftIO (getLiftedRecSel ftc mty us tcs p v)

    let vExpr = noLoc (mkHsWrap w' (HsVar noExtField (noLoc v')))
    e <- case p of
      RecSelData tc
        -- translate any newtype  record selector "sel" to "return (fmap sel)"
        | isNewTyCon tc -> mkApp (mkNewFmapTh arg) res [vExpr]
        -- translate any datatype record selector "sel" to "return (>>= sel)"
      _                 -> noLoc . flip (SectionR noExtField) vExpr <$>
                             mkAppWith (mkNewBindTh arg) given (bindingType res) []
    ety <- getTypeOrPanic e
    mkApp mkNewReturnTh ety [noLoc (HsPar noExtField e)]
  | otherwise          = do
  -- lift type
  w' <- liftWrapperTcM tcs w
  mtc <- getMonadTycon
  us <- getUniqueSupplyM
  ftc <- getFunTycon
  ty' <- liftIO (liftTypeIfRequired ftc mtc us tcs (varType v))

  let apps = collectTyApps w'


  -- 1. If it is a typeclass operation, we re-create it from scratch to get
  --    the unfolding information right.
  -- 2. If it is a LclId, just use the lifted type.
  -- 3. If it is a default method
  --    (guaranteed to be imported, otherwise 2 applies),
  --    we have to set the correct type and
  --    switch to the correct default method
  -- 4. If it is one of a specific set of methods from the Prelude
  --    (due to deriving), we have to switch to the correct method.
  --    This falls back to jus returning the current identifier,
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
            return (mkDictSelId (sels' !! idx) cls')
          | isLocalId v =
            return (setVarType v ty')
          | '$':'d':'m':_ <- occNameString (occName v) = do
            -- Split the type to get the class that this is the default method
            -- for, and look up the new version of that class.
            let tc = tyConAppTyCon (funArgTy (snd (splitForAllTys (varType v))))
            tc' <- liftIO (lookupTyConMap GetNew tcs tc)
            if tc == tc' -- if they are equal, this is NOT a built-in class.
              then -- Thus, v is almost typed correctly.
                setVarType v <$> liftIO (replaceTyconTy tcs (varType v))
              -- Otherwise, do stuff
              else
                let defMethName = tyConClass_maybe tc' >>= find defLike . classOpItems
                    defLike (_ , Just (n', _)) = isLiftedDefaultName (occName v) (occName n')
                    defLike _                  = False
                in case defMethName of
                  Just (_, Just (newnm, _)) -> lookupId newnm
                  _ -> failWithTc (ppr (v, tc'))
          | otherwise = lookupWiredInFunc v ty'
  v' <- mv'

  let monotype = instantiateWith apps (varType v')
      getPred (Anon _ t) = Just t
      getPred _          = Nothing
      preds = mapMaybe getPred (fst (splitPiTysInvisible monotype))

  if null preds
    then do
      let newWrap = createWrapperFor (varType v') apps []
      return (noLoc (HsWrap noExtField newWrap (HsVar noExtField (noLoc v'))))
    else do
      -- construct wanted constraints
      wanted <- newWanteds (OccurrenceOf (varName v')) preds
      let evvars = map (\a -> case ctev_dest a of { EvVarDest d -> d; HoleDest (CoercionHole d _ ) -> d }) wanted
      let cts = map CNonCanonical wanted
      -- solve them
      evidence <- mkWpLet . EvBinds <$>
        simplifyTop (WC (listToBag (cts ++ given)) emptyBag)

      -- create the new wrapper, with the new dicts and the type applications
      let wdict = createWrapperFor (varType v') apps evvars
      let wall = HsWrap noExtField (evidence <.> wdict)
      zonkTopLExpr (noLoc $ wall $ HsVar noExtField $ noLoc v')

-- (,b,) = return $ \x1 -> return $ \x2 -> return (x1, b, x2)
liftExplicitTuple :: [Ct] -> TyConMap -> [LHsTupArg GhcTc]
                  -> Boxity -> TcM (LHsExpr GhcTc)
liftExplicitTuple given tcs args b = liftExplicitTuple' [] WpHole args
  where
    liftExplicitTuple' :: [LHsExpr GhcTc] -> HsWrapper -> [LHsTupArg GhcTc]
                       -> TcM (LHsExpr GhcTc)
    liftExplicitTuple' col w (L _ (XTupArg _) : xs) =
      liftExplicitTuple' col w xs
    liftExplicitTuple' col w (L _ (Present _ e) : xs) = do
      e' <- liftMonadicExpr given tcs e
      ty <- getTypeOrPanic e'
      liftExplicitTuple' (e' : col) (WpTyApp (bindingType ty) <.> w) xs
    liftExplicitTuple' col w (L _ (Missing ty) : xs) = do
      ty' <- liftTypeTcM tcs ty
      v <- noLoc <$> freshVar ty'
      let arg = noLoc (HsVar noExtField v)
      inner <- liftExplicitTuple' (arg:col) (WpTyApp (bindingType ty') <.> w) xs
      resty <- getTypeOrPanic inner
      let lam = mkLam v ty inner resty
      mkApp mkNewReturnTh (mkVisFunTy ty' resty) [lam]
    liftExplicitTuple' col w [] = do
      let exprArgs = reverse col
      dc <- liftIO (getLiftedCon (tupleDataCon b (length exprArgs)) tcs)
      let ce = HsWrap noExtField w (HsConLikeOut noExtField (RealDataCon dc))
      let appCe = foldl mkHsApp (noLoc ce) exprArgs
      ty <- getTypeOrPanic appCe
      mkApp mkNewReturnTh ty [appCe]

-- This is for RecordConstructors only.
-- We are interested in lifting the (potential wrapper)
-- and we want to replace the HsConLike with the lifted constructor version.
-- HsConLike is the only sensible option for this PostTcExpr for Haskell2010.
liftConExpr :: TyConMap -> DataCon -> PostTcExpr -> TcM PostTcExpr
liftConExpr tcs dc (HsWrap _ w _) = do
  w' <- liftWrapperTcM tcs w
  return (HsWrap noExtField w' (HsConLikeOut noExtField (RealDataCon dc)))
liftConExpr _ dc _ = return (HsConLikeOut noExtField (RealDataCon dc))

liftMonadicRecFields :: [Ct] -> TyConMap
                     -> HsRecordBinds GhcTc
                     -> TcM (HsRecordBinds GhcTc)
liftMonadicRecFields given tcs (HsRecFields flds dotdot) =
  flip HsRecFields dotdot <$> mapM (liftMonadicRecField given tcs) flds

liftMonadicRecordUpd :: TyConMap -> RecordUpdTc -> TcM RecordUpdTc
liftMonadicRecordUpd tcs (RecordUpdTc cs intys outtys wrap) =
  RecordUpdTc <$> mapM conLike cs
            <*> mapM (liftInnerTyTcM tcs) intys
            <*> mapM (liftInnerTyTcM tcs) outtys
            <*> liftWrapperTcM tcs wrap
  where
    conLike (RealDataCon c) = RealDataCon <$> liftIO (getLiftedCon c tcs)
    conLike p@(PatSynCon _) = do
      flags <- getDynFlags
      reportError (mkErrMsg flags noSrcSpan neverQualify
        "Pattern synonyms are not supported by the plugin")
      failIfErrsM
      return p

liftMonadicRecordUpdField :: [Ct] -> TyConMap -> LHsRecUpdField GhcTc
                          -> TcM (LHsRecUpdField GhcTc)
liftMonadicRecordUpdField given tcs (L l1 (HsRecField (L l2 ambOcc) e pun)) = do
  ambOcc' <- liftAmbiguousFieldOcc tcs ambOcc
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField (L l2 ambOcc') e' pun))

liftMonadicRecField :: [Ct] -> TyConMap
                    -> LHsRecField GhcTc (LHsExpr GhcTc)
                    -> TcM (LHsRecField GhcTc (LHsExpr GhcTc))
liftMonadicRecField given tcs (L l1 (HsRecField (L l2 occ) e pun)) = do
  occ' <- liftFieldOcc tcs occ
  e' <- liftMonadicExpr given tcs e
  return (L l1 (HsRecField (L l2 occ') e' pun))

-- for some weird reason, the "v" is not a selector function.
-- (It should be according to the doumentation)
-- By looking it up in the type environment again, we fix this.
liftFieldOcc :: TyConMap -> FieldOcc GhcTc -> TcM (FieldOcc GhcTc)
liftFieldOcc tcs (FieldOcc v _) = do
  tenv <- tcg_type_env <$> getGblEnv
  Just (AnId realV) <- return $ lookupTypeEnv tenv (varName v)
  case idDetails realV of
    RecSelId parent _ -> do
      mty <- mkTyConTy <$> getMonadTycon
      us <- getUniqueSupplyM
      ftc <- getFunTycon
      v' <- liftIO (getLiftedRecSel ftc mty us tcs parent v)
      return (FieldOcc v' (noLoc (nameRdrName (varName v'))))
    _ -> panicBndr "Expected RecSel in FieldOcc of Record operation" v
liftFieldOcc _ occ = return occ

liftAmbiguousFieldOcc :: TyConMap -> AmbiguousFieldOcc GhcTc
                      -> TcM (AmbiguousFieldOcc GhcTc)
liftAmbiguousFieldOcc tcs (Unambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs (FieldOcc v n)
  return (Unambiguous v' n')
liftAmbiguousFieldOcc tcs (Ambiguous v n) = do
  FieldOcc v' n' <- liftFieldOcc tcs (FieldOcc v n)
  return (Ambiguous v' n')
liftAmbiguousFieldOcc _ x = return x

liftTick :: TyConMap -> Tickish Var -> TcM (Tickish Var)
liftTick tcs (Breakpoint i ids) = Breakpoint i <$> mapM transId ids
  where
    transId v = setVarType v <$> liftTypeTcM tcs (varType v)
liftTick _ t = return t

shareVars :: [(Var, Var)] -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
shareVars vs e' =
  foldM shareVar e' vs
  where
    -- share v1 >>= \v2 -> e
    shareVar e (v1,v2) = return (substitute v1 v2 e)

substitute :: Data a => Var -> Var -> a -> a
substitute new old = everywhere (mkT substVar)
 where
    u = varName old
    substVar v = if varName v == u then new else v

{- HLINT ignore "Reduce duplication" -}
