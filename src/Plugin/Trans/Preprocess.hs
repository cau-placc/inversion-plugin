{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
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
import Data.Generics (everywhereM, mkM)
import Data.Map.Strict
import Data.List (isPrefixOf)
import Data.Maybe
import Control.Monad.State
import qualified Language.Haskell.TH as TH

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Expr
import GHC.Hs.Pat
import GHC.Hs.Lit
import GHC.Hs.Types
import TcRnMonad
import TcEvidence
import SrcLoc
import GhcPlugins
import ErrUtils
import Unique
import Finder
import IfaceEnv
import PrimOp (tagToEnumKey)
import PrelNames

import Plugin.Trans.Util
import Plugin.Trans.Var
import Plugin.Trans.PatternMatching
import Plugin.Trans.Type
import Plugin.BuiltIn (notFL)

type PM = StateT (Map Unique Name) TcM

instance Ord Unique where
  compare = nonDetCmpUnique

instance HasDynFlags (StateT s TcM) where
  getDynFlags = lift getDynFlags

instance MonadUnique (StateT s TcM) where
  getUniqueSupplyM = lift getUniqueSupplyM

rename :: Var -> PM Var
rename v
  | '$':'d':_<- occNameString (occName v) = return v
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
preprocessBinding :: Bool -> HsBindLR GhcTc GhcTc -> PM (HsBindLR GhcTc GhcTc)
preprocessBinding lcl (AbsBinds a b c d e f g)
  -- Record selectors should stay like they are for now.
  | any (isRecordSelector . abe_poly) d = do
      let preprocessExportRec (ABE x p m w sp) =
            renameRec p >>= \p' -> return (ABE x p' m w sp)
          preprocessExportRec x = return x

      d' <- mapM preprocessExportRec d
      return (AbsBinds a b c d' e f g)
  | any (isDictFun . abe_poly) d = do
      bs <- liftBag (preprocessBinding lcl) f
      return (AbsBinds a b c d e bs g)
  | otherwise = do
      -- Preprocess each binding seperate.
      bs <- liftBag (preprocessBinding lcl) f
      d' <- mapM preprocessExport d
      return (AbsBinds a b c d' e bs g)
  where
    isDictFun v = case occNameString (occName v) of
      '$':'f':_ -> True
      _         -> False
preprocessBinding lcl (FunBind a (L b name) eqs c ticks) = do
  -- Compile pattern matching first, but only use matchExpr
  -- if this is a top-level binding to avoid doing this multiple times.
  Left matchedGr <- lift (compileMatchGroup eqs)
  matched <- (if lcl then return else lift . everywhereM (mkM matchExpr)) matchedGr
  -- Preprocess the inner part of the declaration afterwards.
  eqs' <- preprocessEquations matched
  name' <- rename name
  return (FunBind a (L b name') eqs' c ticks)
preprocessBinding _ (VarBind x v e inl) = do
  e' <- preprocessExpr e
  v' <- rename v
  return (VarBind x v' e' inl)
preprocessBinding _ a = panicAny "unexpected binding type" a

preprocessExport :: ABExport GhcTc -> PM (ABExport GhcTc)
preprocessExport (ABE x p m w s) =
  ABE x <$> rename p <*> rename m <*> pure w <*> pure s
preprocessExport x = return x

preprocessEquations :: MatchGroup GhcTc (LHsExpr GhcTc)
                    -> PM (MatchGroup GhcTc (LHsExpr GhcTc))
preprocessEquations (MG a (L b alts) c) = do
  alts' <- mapM preprocessAlt alts
  return (MG a (L b alts') c)
preprocessEquations a = return a

preprocessAlt :: LMatch GhcTc (LHsExpr GhcTc)
              -> PM (LMatch GhcTc (LHsExpr GhcTc))
preprocessAlt (L a (Match b c d rhs)) = do
  ctxt <- preprocessMatchCtxt c
  rhs' <- preprocessRhs rhs
  d' <- mapM preprocessPat d
  return (L a (Match b ctxt d' rhs'))
preprocessAlt a = return a

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
  ConPatIn _ _        -> panicAny "Cannot handle such a pattern" p
  ConPatOut {}        -> (\x -> p { pat_args = x })
                            <$> preprocessConDetails (pat_args p)
  ViewPat x e p'      -> ViewPat x <$> preprocessExpr e <*> preprocessPat p'
  SplicePat _ _       -> panicAny "Cannot handle such a pattern" p
  LitPat {}           -> return p
  NPat {}             -> panicAny "Cannot handle such a pattern" p
  NPlusKPat {}        -> panicAny "Cannot handle such a pattern" p
  SigPat x p' s       -> SigPat x <$> preprocessPat p' <*> pure s
  CoPat {}            -> panicAny "Cannot handle such a pattern" p
  XPat _              -> panicAny "Cannot handle such a pattern" p

preprocessConDetails :: HsConPatDetails GhcTc -> PM (HsConPatDetails GhcTc)
preprocessConDetails (PrefixCon args) = PrefixCon <$> mapM preprocessPat args
preprocessConDetails (RecCon (HsRecFields flds dd)) =
  (RecCon .) . HsRecFields <$> mapM preprocessFieldP flds <*> pure dd
preprocessConDetails (InfixCon arg1 arg2) = InfixCon <$> preprocessPat arg1 <*> preprocessPat arg2

preprocessFieldP :: Located (HsRecField' a (LPat GhcTc))
                 -> PM (Located (HsRecField' a (LPat GhcTc)))
preprocessFieldP (L l (HsRecField v e p)) = do
  e' <- preprocessPat e
  return (L l (HsRecField v e' p))

preprocessMatchCtxt :: HsMatchContext Name -> PM (HsMatchContext Name)
preprocessMatchCtxt (FunRhs (L l idt) x y) = do
  v <- renameName idt
  return (FunRhs (L l v) x y)
preprocessMatchCtxt x = return x

preprocessRhs :: GRHSs GhcTc (LHsExpr GhcTc)
              -> PM (GRHSs GhcTc (LHsExpr GhcTc))
preprocessRhs (GRHSs a grhs b) = do
  grhs' <- mapM preprocessGRhs grhs
  return (GRHSs a grhs' b)
preprocessRhs a = return a

preprocessGRhs :: LGRHS GhcTc (LHsExpr GhcTc)
               -> PM (LGRHS GhcTc (LHsExpr GhcTc))
preprocessGRhs (L a (GRHS b c body)) = do
  body' <- preprocessExpr body
  return (L a (GRHS b c body'))
preprocessGRhs a = return a

isBuiltIn :: Name -> Bool
isBuiltIn nm =
  "krep$" `isPrefixOf` str ||
  "$tc"   `isPrefixOf` str ||
  "$dm"   `isPrefixOf` str ||
  ("noMethodBindingError" == str  && nameModule_maybe nm == Just cONTROL_EXCEPTION_BASE) ||
  ("recSelError"  == str && nameModule_maybe nm == Just cONTROL_EXCEPTION_BASE) ||
  ("undefined"  == str && nameModule_maybe nm == Just gHC_ERR) ||
  ("error" == str && nameModule_maybe nm == Just gHC_ERR) ||
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
preprocessExpr (L l (HsWrap _ w1 (HsAppType _ (L _ (HsWrap _ w2 e)) _))) = do
  e' <- preprocessExpr (L l e)
  return (L l (HsWrap noExtField (w1 <.> w2) (unLoc e')))
preprocessExpr e@(L l1 (HsVar x (L l2 v))) = do
  let nm = varName v
  mdl <- tcg_mod <$> lift getGblEnv
  if nameIsLocalOrFrom mdl nm
    then L l1 . HsVar x . L l2 <$> rename v
    else case nameModule_maybe nm of
      Just mdl' | not $ isBuiltIn nm -> do
          hsc <- lift getTopEnv
          let unitID = moduleUnitId mdl'
          let pluginModName = mkModuleName $ fromJust $ TH.nameModule 'notFL
          mbprel <- liftIO $ findImportedModule hsc pluginModName Nothing
          prel <- case mbprel of
            Found _ m -> return m
            _         -> lift $ failWithTc "Could not find module for built-in primitives"
          let definiteMdl = if unitID == baseUnitId || unitID == primUnitId
                              then prel
                              else mdl'
          let definiteName = addNameSuffix (occName nm)
          mv <- lift $ lookupByOccName definiteMdl definiteName
          lift $ case mv of
            Just v' -> return (L l1 (HsVar x (L l2 (v' `setVarType` varType v))))
            Nothing -> failWithTc ("No inverse available for:" <+> ppr nm)
      _   -> return e
preprocessExpr e@(L _ HsLit{}) =
  return e
preprocessExpr (L l (HsOverLit x lit)) =
  (\e -> L l (HsOverLit x (lit { ol_witness = unLoc e })))
    <$> preprocessExpr (noLoc (ol_witness lit))
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
preprocessExpr (L l (HsAppType x e ty)) = do
  e' <- preprocessExpr e
  return (L l (HsAppType x e' ty))
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
preprocessExpr e@(L l ExplicitSum {}) = do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
    "Unboxed sum types are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr (L l (HsCase x sc br)) = do
  br' <- preprocessEquations br
  sc' <- preprocessExpr sc
  return (L l (HsCase x sc' br'))
preprocessExpr (L l (HsIf x Nothing e1 e2 e3)) = do
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  e3' <- preprocessExpr e3
  return (L l (HsIf x Nothing e1' e2' e3'))
preprocessExpr (L l (HsIf x (Just se) e1 e2 e3)) = do
  se' <- preprocessSynExpr se
  e1' <- preprocessExpr e1
  e2' <- preprocessExpr e2
  e3' <- preprocessExpr e3
  return (L l (HsIf x (Just se') e1' e2' e3'))
preprocessExpr e@(L _ (HsMultiIf _ _)) =
  panicAny "Multi-way if should have been desugared before lifting" e
preprocessExpr (L l (HsLet x bs e)) = do
  bs' <- preprocessLocalBinds bs
  e' <- preprocessExpr e
  return (L l (HsLet x bs' e'))
preprocessExpr (L l1 (HsDo x ctxt (L l2 stmts))) = do
  stmts' <- preprocessStmts stmts
  return (L l1 (HsDo x ctxt (L l2 stmts')))
preprocessExpr (L l (ExplicitList x Nothing es)) = do
  es' <- mapM preprocessExpr es
  return (L l (ExplicitList x Nothing es'))
preprocessExpr e@(L l (ExplicitList _ (Just _) _)) = do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr (L l (RecordCon x cn (HsRecFields flds dd))) = do
  flds' <- mapM preprocessField flds
  return (L l (RecordCon x cn (HsRecFields flds' dd)))
preprocessExpr (L l (RecordUpd x e flds)) = do
  e' <- preprocessExpr e
  flds' <- mapM preprocessField flds
  return (L l (RecordUpd x e' flds'))
preprocessExpr (L l (ExprWithTySig x e ty)) = do
  e' <- preprocessExpr e
  return (L l (ExprWithTySig x e' ty))
preprocessExpr (L l (ArithSeq x Nothing i)) = do
  x' <- unLoc <$> preprocessExpr (noLoc x)
  i' <- preprocessArithExpr i
  return (L l (ArithSeq x' Nothing i'))
preprocessExpr e@(L l (ArithSeq _ (Just _) _)) = do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr (L l (HsSCC a b c e)) = do
  e' <- preprocessExpr e
  return (L l (HsSCC a b c e'))
preprocessExpr (L l (HsCoreAnn a b c e)) = do
  e' <- preprocessExpr e
  return (L l (HsCoreAnn a b c e'))
preprocessExpr e@(L l (HsBracket _ _)) = do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L l (HsSpliceE _ _)) =  do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L l HsTcBracketOut {}) = do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
    "Template Haskell and Quotation are not supported by the plugin")
  lift failIfErrsM
  return e
preprocessExpr e@(L l HsProc {}) =  do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
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
preprocessExpr (L l (HsTickPragma a b c d e)) = do
  e' <- preprocessExpr e
  return (L l (HsTickPragma a b c d e'))
preprocessExpr (L l (HsWrap x w e)) = do
  e' <- unLoc <$> preprocessExpr (noLoc e)
  return (L l (HsWrap x w e'))
preprocessExpr e = panicAny "This expression should not occur after TC" e

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
    preprocessStmt (L l (LastStmt x e a r)) = do
      e' <- preprocessExpr e
      r' <- preprocessSynExpr r
      return (L l (LastStmt x e' a r'))
    preprocessStmt (L l (BindStmt x p e b f)) = do
      e' <- preprocessExpr e
      b' <- preprocessSynExpr b
      f'  <- preprocessSynExpr f
      return (L l (BindStmt x p e' b' f'))
    preprocessStmt (L l ApplicativeStmt {}) = do
      flags <- getDynFlags
      lift $ reportError (mkErrMsg flags l neverQualify
        "Applicative do-notation is not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt (L l (BodyStmt x e sq g)) = do
      e'  <- preprocessExpr e
      sq' <- preprocessSynExpr sq
      g'  <- preprocessSynExpr g
      return (L l (BodyStmt x e' sq' g'))
    preprocessStmt (L l (LetStmt x bs)) = do
      bs' <- preprocessLocalBinds bs
      return (L l (LetStmt x bs'))
    preprocessStmt (L l ParStmt {}) =  do
      flags <- getDynFlags
      lift $ reportError (mkErrMsg flags l neverQualify
        "Parallel list comprehensions are not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt (L l TransStmt {}) = do
      flags <- getDynFlags
      lift $ reportError (mkErrMsg flags l neverQualify
        "Transformative list comprehensions are not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt (L l RecStmt {}) =  do
      flags <- getDynFlags
      lift $ reportError (mkErrMsg flags l neverQualify
        "Recursive do-notation is not supported by the plugin")
      lift failIfErrsM
      return s
    preprocessStmt s' = return s'

preprocessSynExpr :: SyntaxExpr GhcTc -> PM (SyntaxExpr GhcTc)
preprocessSynExpr (SyntaxExpr e ws w) = do
  e' <- unLoc <$> preprocessExpr (noLoc e)
  return (SyntaxExpr e' ws w)

preprocessField :: Located (HsRecField' a (LHsExpr GhcTc))
                -> PM (Located (HsRecField' a (LHsExpr GhcTc)))
preprocessField (L l (HsRecField v e p)) = do
  e' <- preprocessExpr e
  return (L l (HsRecField v e' p))

preprocessTupleArg :: LHsTupArg GhcTc -> PM (LHsTupArg GhcTc)
preprocessTupleArg (L l (Present x e)) =
  L l . Present x <$> preprocessExpr e
preprocessTupleArg x = return x

preprocessLocalBinds :: LHsLocalBinds GhcTc -> PM (LHsLocalBinds GhcTc)
preprocessLocalBinds (L l (HsValBinds x b)) = do
  b' <- preprocessValBinds b
  return (L l (HsValBinds x b'))
preprocessLocalBinds bs@(L l (HsIPBinds _ _)) =  do
  flags <- getDynFlags
  lift $ reportError (mkErrMsg flags l neverQualify
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
      bs' <- liftBag (preprocessBinding True) b
      return (rf, bs')
