{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
{-# OPTIONS_GHC -Wno-orphans   #-}
{-|
Module      : Plugin.Trans.Preprocess
Description : Simplify functions to prepare for lifting
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module simplifies functions to prepare them for the lifting phase.
At its core, this phase simplifies pattern matching and does a few minor
rewrites of selected expressions.
-}
module Plugin.Trans.Preprocess (preprocessBinding) where

import Prelude hiding (lookup)
import Data.Char
import Data.Generics (everywhereM, mkM)
import Data.Map.Strict
import Data.List (isPrefixOf)
import Control.Monad.State

import GHC.Hs.Binds
import GHC.Hs.Expr
import GHC.Hs.Extension
import GHC.Hs.Lit
import GHC.Hs
import GHC.Plugins
import GHC.Tc.Types
import GHC.Tc.Types.Evidence
import GHC.Tc.Utils.Monad
import GHC.Types.Unique
import GHC.Unit.Finder
import GHC.Data.Bag
import GHC.Builtin.Names
import GHC.Builtin.PrimOps
import GHC.Types.TyThing
import GHC.Iface.Env
import GHC.Types.Error

import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Trans.PatternMatching
import Plugin.Trans.Type
import Plugin.Trans.Import

type PM = StateT (Map Unique Name) TcM

instance Ord Unique where
  compare = nonDetCmpUnique

instance HasDynFlags (StateT s TcM) where
  getDynFlags = lift getDynFlags

instance MonadUnique (StateT s TcM) where
  getUniqueSupplyM = lift getUniqueSupplyM

rename :: Var -> PM Var
rename v
  | '$':'d':x:_ <- occNameString (occName v), isUpper x = return v
  | isRecordSelector v = renameRec v
  | otherwise = get >>= \s -> case lookup (varUnique v) s of
    Nothing -> do
      u <- getUniqueM
      let n' = liftName (varName v) u
      put (insert (varUnique v) n' s)
      return (setVarUnique (setVarName v n') u)
    Just n ->
      return (setVarUnique (setVarName v n) (nameUnique n))

renameRec :: Var -> PM Var
renameRec v  = get >>= \s -> case lookup (varUnique v) s of
    Nothing -> do
      u <- getUniqueM
      let n = varName v
      let o = occName v
      let o' = mkOccName (occNameSpace o) (occNameString o ++ "$FLsel")
      let n' = tidyNameOcc (setNameUnique n u) o'
      put (insert (varUnique v) n' s)
      return (setVarUnique (setVarName v n') u)
    Just n ->
      return (setVarUnique (setVarName v n) (nameUnique n))

renameName :: Name -> PM Name
renameName v = get >>= \s -> case lookup (nameUnique v) s of
  Nothing -> do
    u <- getUniqueM
    let n' = liftName v u
    put (insert (nameUnique v) n' s)
    return n'
  Just n  ->
    return n

-- | Preprocess a binding before lifting, to get rid of nested pattern matching.
-- Also removes some explicit type applications and fuses HsWrapper.
preprocessBinding :: Bool -> HsBindLR GhcTc GhcTc -> PM [HsBindLR GhcTc GhcTc]
preprocessBinding lcl (AbsBinds a b c d e f g)
  -- Record selectors should stay like they are for now.
  | any (isRecordSelector . abe_poly) d = do
      let preprocessExportRec (ABE x p m w sp) =
            renameRec p >>= \p' -> return (ABE x p' m w sp)
          preprocessExportRec x = return x

      d' <- mapM preprocessExportRec d
      return [AbsBinds a b c d' e f g]
  | any (isDictFun . abe_poly) d = do
      bs <- listToBag <$> concatMapM (\(L l bind) -> Prelude.map (L l) <$> preprocessBinding lcl bind) (bagToList f)
      return [AbsBinds a b c d e bs g]
  | otherwise = do
      -- Preprocess each binding seperate.
      bs <- listToBag <$> concatMapM (\(L l bind) -> Prelude.map (L l) <$> preprocessBinding lcl bind) (bagToList f)
      d' <- mapM preprocessExport d
      return [AbsBinds a b c d' e bs g]
  where
    isDictFun v = case occNameString (occName v) of
      '$':'f':_ -> True
      _         -> False
preprocessBinding lcl (FunBind a (L b name) eqs ticks) = do
  -- Compile pattern matching first, but only use matchExpr
  -- if this is a top-level binding to avoid doing this multiple times.
  Left matchedGr <- lift (compileMatchGroup eqs)
  matched <- (if lcl then return else lift . everywhereM (mkM matchExpr)) matchedGr
  -- Preprocess the inner part of the declaration afterwards.
  eqs' <- preprocessEquations matched
  name' <- rename name
  return [FunBind a (L b name') eqs' ticks]
preprocessBinding _ (VarBind x v e) = do
  e' <- preprocessExpr e
  v' <- rename v
  return [VarBind x v' e']
preprocessBinding _ (PatBind ty p grhs ticks) = do
  p' <- preprocessPat p
  grhs' <- preprocessRhs grhs
  (\(x, _, _) -> Prelude.map unLoc x) <$> lift (compileLetBind (noLocA (PatBind ty p' grhs' ticks)))
preprocessBinding _ a = panicAny "unexpected binding type" a

preprocessExport :: ABExport GhcTc -> PM (ABExport GhcTc)
preprocessExport (ABE x p m w s) =
  ABE x <$> rename p <*> rename m <*> pure w <*> pure s

preprocessEquations :: MatchGroup GhcTc (LHsExpr GhcTc)
                    -> PM (MatchGroup GhcTc (LHsExpr GhcTc))
preprocessEquations (MG a (L b alts) c) = do
  alts' <- mapM preprocessAlt alts
  return (MG a (L b alts') c)

preprocessAlt :: LMatch GhcTc (LHsExpr GhcTc)
              -> PM (LMatch GhcTc (LHsExpr GhcTc))
preprocessAlt (L a (Match b c d rhs)) = do
  ctxt <- preprocessMatchCtxt c
  rhs' <- preprocessRhs rhs
  d' <- mapM preprocessPat d
  return (L a (Match b ctxt d' rhs'))

preprocessPat :: LPat GhcTc -> PM (LPat GhcTc)
preprocessPat (L l p) = L l <$> case p of
  WildPat {}           -> return p
  VarPat x (L l2 v)   -> VarPat x . L l2 <$> rename v
  LazyPat x p'        -> LazyPat x <$> preprocessPat p'
  AsPat x (L l2 v) p' -> AsPat x . L l2 <$> rename v <*> preprocessPat p'
  ParPat x p'         -> ParPat x <$> preprocessPat p'
  BangPat x p'        -> BangPat x <$> preprocessPat p'
  ListPat x ps        -> ListPat x <$> mapM preprocessPat ps
  TuplePat x ps b     -> TuplePat x <$> mapM preprocessPat ps <*> pure b
  SumPat x p' t a     -> SumPat x <$> preprocessPat p' <*> pure t <*> pure a
  ConPat {}           -> (\x -> p { pat_args = x })
                            <$> preprocessConDetails (pat_args p)
  ViewPat x e p'      -> ViewPat x <$> preprocessExpr e <*> preprocessPat p'
  SplicePat _ _       -> panicAny "Cannot handle such a pattern" p
  LitPat {}           -> return p
  NPat {}             -> panicAny "Cannot handle such a pattern" p
  NPlusKPat {}        -> panicAny "Cannot handle such a pattern" p
  SigPat x p' s       -> SigPat x <$> preprocessPat p' <*> pure s
  XPat _              -> panicAny "Cannot handle such a pattern" p

preprocessConDetails :: HsConPatDetails GhcTc -> PM (HsConPatDetails GhcTc)
preprocessConDetails (PrefixCon tyargs args) = PrefixCon tyargs <$> mapM preprocessPat args
preprocessConDetails (RecCon (HsRecFields flds dd)) =
  (RecCon .) . HsRecFields <$> mapM preprocessFieldP flds <*> pure dd
preprocessConDetails (InfixCon arg1 arg2) = InfixCon <$> preprocessPat arg1 <*> preprocessPat arg2

preprocessFieldP :: XRec GhcTc (HsRecField' a (LPat GhcTc))
                 -> PM (XRec GhcTc  (HsRecField' a (LPat GhcTc)))
preprocessFieldP (L l (HsRecField a v e p)) = do
  e' <- preprocessPat e
  return (L l (HsRecField a v e' p))

preprocessMatchCtxt :: HsMatchContext GhcRn -> PM (HsMatchContext GhcRn)
preprocessMatchCtxt (FunRhs (L l idt) x y) = do
  v <- renameName idt
  return (FunRhs (L l v) x y)
preprocessMatchCtxt x = return x

preprocessRhs :: GRHSs GhcTc (LHsExpr GhcTc)
              -> PM (GRHSs GhcTc (LHsExpr GhcTc))
preprocessRhs (GRHSs a grhs b) = do
  grhs' <- mapM preprocessGRhs grhs
  return (GRHSs a grhs' b)

preprocessGRhs :: LGRHS GhcTc (LHsExpr GhcTc)
               -> PM (LGRHS GhcTc (LHsExpr GhcTc))
preprocessGRhs (L a (GRHS b c body)) = do
  body' <- preprocessExpr body
  return (L a (GRHS b c body'))

isBuiltIn :: Name -> Bool
isBuiltIn nm =
  "krep$" `isPrefixOf` str ||
  "$tc"   `isPrefixOf` str ||
  "$dm"   `isPrefixOf` str ||
  ("noMethodBindingError" == str  && nameModule_maybe nm == Just cONTROL_EXCEPTION_BASE) ||
  ("recSelError"  == str && nameModule_maybe nm == Just cONTROL_EXCEPTION_BASE) ||
  ("undefined"  == str && nameModule_maybe nm == Just gHC_ERR) ||
  ("error" == str && nameModule_maybe nm == Just gHC_ERR) ||
  ("dataToTag#" == str && nameModule_maybe nm == Just gHC_PRIM) ||
  nameUnique nm == tagToEnumKey ||
  nameUnique nm == coerceKey
  where
    str = occNameString (occName nm)

lookupByOccName :: Module -> OccName -> TcM (Maybe Var)
lookupByOccName mdl occ = discardErrs $ recoverM
  (return Nothing)
  (do v <- lookupId =<< lookupOrig mdl occ
      (ty, _) <- removeNondet (varType v)
      return (Just (setVarType v ty)))

-- preprocessExpr traverses the AST to reach all local function definitions
-- and removes some ExplicitTypeApplications.
-- Some HsWrapper might be split into two halves on each side of an
-- explicit type applications. We have to fuse those wrappers.
preprocessExpr :: LHsExpr GhcTc -> PM (LHsExpr GhcTc)
preprocessExpr e@(L l1 (HsVar x (L l2 v))) = do
  let nm = varName v
  mdl <- tcg_mod <$> lift getGblEnv
  if nameIsLocalOrFrom mdl nm
    then L l1 . HsVar x . L l2 <$> rename v
    else case nameModule_maybe nm of
      Just mdl' | not $ isBuiltIn nm -> do
          hsc <- lift getTopEnv
          replacementModule <- case lookupSupportedBuiltInModule mdl' of
            Just s  -> do
              mbprel <- liftIO $ findImportedModule hsc (mkModuleName s) Nothing
              case mbprel of
                Found _ m -> return m
                _         -> lift $ failWithTc $ "Could not find module for built-in primitives of the imported module:" <+> text s
            Nothing -> return mdl'
          let definiteName = addNameSuffix (occName nm)
          mv <- lift $ lookupByOccName replacementModule definiteName
          lift $ case mv of
            Just v' -> return (L l1 (HsVar x (L l2 (v' `setVarType` varType v))))
            Nothing -> failWithTc ("No inverse available for:" <+> ppr nm)
      _   -> return e
preprocessExpr e@(L _ HsLit{}) =
  return e
preprocessExpr (L l (HsOverLit x lit)) =
  (\e -> L l (HsOverLit x (lit { ol_witness = unLoc e })))
    <$> preprocessExpr (noLocA (ol_witness lit))
preprocessExpr (L l (HsLam x mg)) = do
  mg' <- preprocessEquations mg
  return (L l (HsLam x mg'))
preprocessExpr (L l (HsLamCase x mg)) = do
  mg' <- preprocessEquations mg
  return (L l (HsLamCase x mg'))
preprocessExpr e@(L _ (HsConLikeOut _ _)) =
  return e
preprocessExpr (L l (OpApp x e1 op e2)) = do
  e1' <- preprocessExpr e1
  op' <- preprocessExpr op
  e2' <- preprocessExpr e2
  return (L l (OpApp x e1' op' e2'))
preprocessExpr (L l (HsApp x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (L l (HsApp x e1' e2'))
preprocessExpr (L l (HsAppType ty e _)) = do
  e' <- unLoc <$> preprocessExpr e
  case e' of
    (XExpr (WrapExpr (HsWrap w' e''))) ->
         return (L l (XExpr (WrapExpr (HsWrap (WpTyApp ty <.> w') e''))))
    _ -> return (L l (XExpr (WrapExpr (HsWrap (WpTyApp ty) e'))))
preprocessExpr (L l (NegApp x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessSynExpr e2
  return (L l (NegApp x e1' e2'))
preprocessExpr (L l (HsPar x e)) = do
  e' <- preprocessExpr e
  return (L l (HsPar x e'))
preprocessExpr (L l (SectionL x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (L l (SectionL x e1' e2'))
preprocessExpr (L l (SectionR x e1 e2)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (L l (SectionR x e1' e2'))
preprocessExpr (L l (ExplicitTuple x args b)) = do
  args' <- mapM preprocessTupleArg args
  return (L l (ExplicitTuple x args' b))
preprocessExpr e@(L _ ExplicitSum {}) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Unboxed sum types are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr (L l (HsCase x sc br)) = do
  br' <- preprocessEquations br
  sc' <- preprocessExpr sc
  return (L l (HsCase x sc' br'))
preprocessExpr (L l (HsIf x e1 e2 e3)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  e3' <- preprocessExpr e3
  return (L l (HsIf x e1' e2' e3'))
preprocessExpr e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
preprocessExpr (L l (HsLet x bs e)) = do
  bs' <- preprocessLocalBinds (noLoc bs)
  e' <- preprocessExpr e
  return (L l (HsLet x (unLoc bs') e'))
preprocessExpr (L l1 (HsDo x ctxt (L l2 stmts))) = do
  stmts' <- preprocessStmts stmts
  return (L l1 (HsDo x ctxt (L l2 stmts')))
preprocessExpr (L l (ExplicitList x es)) = do
  es' <- mapM preprocessExpr es
  return (L l (ExplicitList x es'))
preprocessExpr (L l (RecordCon x cn (HsRecFields flds dd))) = do
  flds' <- mapM preprocessField flds
  return (L l (RecordCon x cn (HsRecFields flds' dd)))
preprocessExpr (L l (RecordUpd x e flds)) = do
  e' <- preprocessExpr e
  flds' <- either (fmap Left . mapM preprocessField)
                  (fmap Right . mapM preprocessField) flds
  return (L l (RecordUpd x e' flds'))
preprocessExpr (L l (ExprWithTySig x e ty)) = do
  e' <- preprocessExpr e
  return (L l (ExprWithTySig x e' ty))
preprocessExpr (L l (ArithSeq x Nothing i)) = do
  x' <- unLoc <$> preprocessExpr (noLocA x)
  i' <- preprocessArithExpr i
  return (L l (ArithSeq x' Nothing i'))
preprocessExpr e@(L _ (ArithSeq _ (Just _) _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Overloaded lists are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsBracket _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsSpliceE _ _)) =  do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ HsTcBracketOut {}) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ HsProc {}) =  do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Arrow notation is not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr (L l (HsStatic x e)) =
  L l . HsStatic x <$> preprocessExpr e
preprocessExpr (L l (HsTick a tick e)) = do
  e' <- preprocessExpr e
  return (L l (HsTick a tick e'))
preprocessExpr (L l (HsBinTick a b c e)) = do
  e' <- preprocessExpr e
  return (L l (HsBinTick a b c e'))
preprocessExpr e@(L _ (HsUnboundVar _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "what is this? TODO")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsRecFld _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "what is this? TODO")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsOverLabel _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Labels are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsIPVar _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "Implicit parameters are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsGetField _ _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "what is this? TODO")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsProjection _ _) ) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "what is this? TODO")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsRnBracketOut _ _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "what is this? TODO")
  lift failIfErrsM
  return e
preprocessExpr e@(L _ (HsPragE _ _ _)) = do
  lift $ reportError (mkMsgEnvelope (getLocA e) neverQualify
    "what is this? TODO")
  lift failIfErrsM
  return e
preprocessExpr (L l (XExpr (ExpansionExpr (HsExpanded _ tc)))) =
  preprocessExpr (L l tc)
preprocessExpr (L l (XExpr (WrapExpr (HsWrap w e)))) = do
  e' <- unLoc <$> preprocessExpr (noLocA e)
  case e' of
    (XExpr (WrapExpr (HsWrap w' e''))) ->
         return (L l (XExpr (WrapExpr (HsWrap (w <.> w') e''))))
    _ -> return (L l (XExpr (WrapExpr (HsWrap w e'))))

preprocessArithExpr :: ArithSeqInfo GhcTc -> PM (ArithSeqInfo GhcTc)
preprocessArithExpr (From e1) = From <$> preprocessExpr e1
preprocessArithExpr (FromThen e1 e2) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (FromThen e1' e2')
preprocessArithExpr (FromTo e1 e2) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  return (FromTo e1' e2')
preprocessArithExpr (FromThenTo e1 e2 e3) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  e3' <- preprocessExpr e3
  return (FromThenTo e1' e2' e3')

preprocessStmts :: [ExprLStmt GhcTc] -> PM [ExprLStmt GhcTc]
preprocessStmts [] = return []
preprocessStmts (s:ss) = do
  s'  <- preprocessStmt s
  ss' <- preprocessStmts ss
  return (s':ss')
  where
    preprocessStmt :: (ExprLStmt GhcTc) -> PM (ExprLStmt GhcTc)
    preprocessStmt (L l (LastStmt x e a r)) = do
      e' <- preprocessExpr e
      r' <- preprocessSynExpr r
      return (L l (LastStmt x e' a r'))
    preprocessStmt (L l (BindStmt (XBindStmtTc b r m f) p e)) = do
      e' <- preprocessExpr e
      b' <- preprocessSynExpr b
      f'  <- maybe (return Nothing) (fmap Just . preprocessSynExpr) f
      return (L l (BindStmt (XBindStmtTc b' r m f') p e'))
    preprocessStmt (L _ ApplicativeStmt {}) = do
      lift $ reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Applicative do-notation is not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt (L l (BodyStmt x e sq g)) = do
      e'  <- preprocessExpr e
      sq' <- preprocessSynExpr sq
      g'  <- preprocessSynExpr g
      return (L l (BodyStmt x e' sq' g'))
    preprocessStmt (L l (LetStmt x bs)) = do
      bs' <- preprocessLocalBinds (noLoc bs)
      return (L l (LetStmt x (unLoc bs')))
    preprocessStmt (L _ ParStmt {}) =  do
      lift $ reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt (L _ TransStmt {}) = do
      lift $ reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt (L _ RecStmt {}) =  do
      lift $ reportError (mkMsgEnvelope (getLocA s) neverQualify
        "Recursive do-notation is not supported by the plugin")
      lift failIfErrsM
      return s

preprocessSynExpr :: SyntaxExpr GhcTc -> PM (SyntaxExpr GhcTc)
preprocessSynExpr (SyntaxExprTc e ws w) = do
  e' <- unLoc <$> preprocessExpr (noLocA e)
  return (SyntaxExprTc e' ws w)
preprocessSynExpr NoSyntaxExprTc = return NoSyntaxExprTc

preprocessField :: XRec GhcTc (HsRecField' a (LHsExpr GhcTc))
                -> PM (XRec GhcTc (HsRecField' a (LHsExpr GhcTc)))
preprocessField (L l (HsRecField a v e p)) = do
  e' <- preprocessExpr e
  return (L l (HsRecField a v e' p))

preprocessTupleArg :: HsTupArg GhcTc -> PM (HsTupArg GhcTc)
preprocessTupleArg (Present x e) =
  Present x <$> preprocessExpr e
preprocessTupleArg x = return x

preprocessLocalBinds :: GenLocated l (HsLocalBinds GhcTc)
                     -> PM (GenLocated l (HsLocalBinds GhcTc))
preprocessLocalBinds (L l (HsValBinds x b)) = do
  b' <- preprocessValBinds b
  return (L l (HsValBinds x b'))
preprocessLocalBinds bs@(L _ (HsIPBinds _ _)) =  do
  lift $ reportError (mkMsgEnvelope noSrcSpan neverQualify
    "Implicit parameters are not supported by the plugin")
  lift failIfErrsM
  return bs
preprocessLocalBinds b = return b

preprocessValBinds :: HsValBindsLR GhcTc GhcTc
                   -> PM (HsValBindsLR GhcTc GhcTc)
preprocessValBinds bs@ValBinds {} =
  panicAny "Untyped bindings are not expected after TC" bs
preprocessValBinds (XValBindsLR (NValBinds bs sigs)) = do
  bs' <- mapM preprocessNV bs
  return (XValBindsLR (NValBinds bs' sigs))
  where
    preprocessNV :: (RecFlag, LHsBinds GhcTc)
                 -> PM (RecFlag, LHsBinds GhcTc)
    preprocessNV (rf, b) = do
      bs' <- listToBag <$> concatMapM (\(L l bind) -> Prelude.map (L l) <$> preprocessBinding True bind) (bagToList b)
      return (rf, bs')
