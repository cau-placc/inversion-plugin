{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-|
Module      : Plugin.Trans.PatternMatching
Description : Simplify pattern matching
Copyright   : (c) Kai-Oliver Prott (2020)
Maintainer  : kai.prott@hotmail.de

This module simplifies pattern matching for functions, case, let and lambda
expressions as well as do notation.
The pattern match compilation is the main preprocessing phase
before lifting a function.
-}
module Plugin.Trans.PatternMatching (compileMatchGroup, matchExpr) where

import Data.List
import Data.Data     (Data)
import Data.Typeable (Typeable)
import Data.Tuple.Extra
import Data.Generics (mkT, everywhere, listify)
import Control.Monad
import GHC.Classes

import GHC.Hs.Binds
import GHC.Hs.Extension
import GHC.Hs.Pat
import GHC.Hs.Lit
import GHC.Hs.Expr
import GHC.Hs.Types
import SrcLoc
import GhcPlugins
import ConLike
import Finder
import IfaceEnv
import TcRnMonad
import TcEvidence
import TcHsSyn
import PatSyn
import PrelNames
import Bag
import ErrUtils

import Plugin.Trans.Var
import Plugin.Trans.Type
import Plugin.Trans.CreateSyntax
import Plugin.Trans.Util

{-
  Pattern matching done by the classical matrix algorithm, but instead of
  left-to-right semantics, we search for an inductive position
  and match there first.

  Please Note:

  Functions are compiled via `compileMatchGroup`.
  In the case of nullary functions, the result will be an expression instead of
  a MatchGroup. Thats why we need that Either result type.

  Cases are compiled by directly calling compileMatching.
  That function needs list of variables (a singleton list in this case),
  to which any as-patterns will be bound to. Thus, we have to create a
  let-binding for the case-scrutinee, unless it is a variable itself.

  A special case is used if the scrutinee is already a variable.
-}

-- | Simplify any pattern matching in the given expression.
-- Only looks at the top of the expression and simplifies a single
-- case, lambda, let, ... and not any deeper parts of the expression.
matchExpr :: HsExpr GhcTc -> TcM (HsExpr GhcTc)
matchExpr (HsLam x mg) = compileMatchGroup mg >>= \case
  Left mg' -> return (HsLam x mg')
  Right e  -> return (unLoc e)
matchExpr (HsLamCase x mg) = compileMatchGroup mg >>= \case
  Left mg' -> return (HsLam x mg')
  Right e  -> return (unLoc e)
matchExpr (HsCase _ (L _ (HsVar _ (L _ v)))
  (MG (MatchGroupTc _ res) (L _ alts) _)) = do
  e <- errorExpr CaseAlt res >>= compileMatching [v] res alts
  return (unLoc e)
matchExpr (HsCase _ scr (MG (MatchGroupTc [a] res) (L _ alts) _)) = do
  v <- freshVar a
  e <- errorExpr CaseAlt res >>= compileMatching [v] res alts
  return (mkSimpleLet NonRecursive scr e v a)
matchExpr (HsMultiIf ty grhs) = do
  err <- errorExpr IfAlt ty
  unLoc <$> foldM compileGuard err grhs
matchExpr (HsLet _ bs e) = do
  bs' <- compileLet bs
  return (unLoc (foldr toLetExpr e bs'))
matchExpr (HsDo x ctxt (L l stmts)) = do
  (stmts', swapCtxt) <- compileDo x ctxt stmts
  let ctxt' = if swapCtxt then DoExpr else ctxt
  return (HsDo x ctxt' (L l stmts'))
matchExpr e = return e

-- | Translate any pattern in do-notation or comprehensions.
-- Also transforms list comprehensions into monad comprehensions and
-- fills any annotated functions that are missing because of that conversion.
compileDo :: Type -> HsStmtContext Name -> [ExprLStmt GhcTc]
          -> TcM ([ExprLStmt GhcTc], Bool)
compileDo _ GhciStmtCtxt _ = failWithTc $ text
  "Do-Notation in GHCi is not supported with the Curry-Plugin"
compileDo _ _ [] =
  panicAny "Empty do-expression or missing last statement" ()
compileDo ty ctxt [L l (LastStmt x e b r)] = do
  let ty' = fst (splitAppTy ty)
  r' <- case ctxt of
    ListComp -> mkListReturn ty'
    _        -> return r
  return ([L l (LastStmt x e b r')], False)
compileDo _ _ (s@(L _ LastStmt {}) : _) =
  panicAny "Unexpected last statement in do notation" s
compileDo ty ctxt (L l (BindStmt _ p e b' f') : stmts) = do
  -- Compile the rest of the statements and create a do-expression.
  (stmts', swapCtxt) <- compileDo ty ctxt stmts
  let ctxt' = if swapCtxt then DoExpr else ctxt
  let rest = noLoc (HsDo ty ctxt' (noLoc stmts'))

  emty <- getTypeOrPanic e
  let ety = snd (splitAppTy emty)

  -- Create the bind and fail for ListComp.
  let ty' = fst (splitAppTy ty)
  (b, f) <- case ctxt of
    ListComp -> (,) <$> mkListBind ety ty' <*> mkListFail ty'
    _        -> return (b', f')

  -- Create the regular and fail alternatatives
  -- (if f is not noSynExpr, the fail one never gets used).
  v <- noLoc <$> freshVar ety
  let alt = mkSimpleAlt CaseAlt rest [p]
      fe = HsWrap noExtField (syn_res_wrap f)
        (HsApp noExtField (noLoc (syn_expr f))
          (fmap (HsWrap noExtField (head (syn_arg_wraps f)))
            (errorStrStmt ctxt)))
      altFail = mkSimpleAlt CaseAlt (noLoc fe) [noLoc (WildPat ety)]
      -- Check if fail is "noSyntaxExpr" (represented by HsLit).
      alts | HsLit _ _ <- syn_expr f    = [noLoc alt]
           | otherwise                  = [noLoc alt, noLoc altFail]
      mgtc = MatchGroupTc [ety] ty
      mg = MG mgtc (noLoc alts) Generated
  e' <- matchExpr (HsCase noExtField (noLoc (HsVar noExtField v)) mg)
  return ([L l (BindStmt ty (noLoc (VarPat noExtField v)) e b noSyntaxExpr),
          noLoc (LastStmt noExtField (noLoc e') False noSyntaxExpr)],
          -- Normally ListCompr creates a return around LastStmt.
          -- Prevent creation of duplicate return for MonadCompr
          -- due to nested LastStmt by changing the context.
          case ctxt of { ListComp -> True; _ -> False })
compileDo ty ctxt (L _ (LetStmt _ bs) : xs) = do
  bs' <- compileLet bs
  let lets = map toLetStmt bs'
  (xs', swapCtxt) <- compileDo ty ctxt xs
  return (lets ++ xs', swapCtxt)
compileDo _ _ (L l ApplicativeStmt {} : _) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Applicative do-notation is not supported by the plugin")
  failIfErrsM
  return ([], False)
compileDo ty ctxt (L l (BodyStmt x e s g) : xs) = do
  (xs', swapCtxt) <- compileDo ty ctxt xs
  -- Add the missing sequence operator (>>) for list comprehensions.
  let ty' = fst (splitAppTy ty)
  (s', g') <- case ctxt of
    ListComp -> (,) <$> mkListSeq unitTy ty' <*> mkListGuard
    _        -> return (s, g)
  return (L l (BodyStmt x e s' g'):xs', swapCtxt)
compileDo _ _ (L l ParStmt {} : _) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Parallel list comprehensions are not supported by the plugin")
  failIfErrsM
  return ([], False)
compileDo _ _ (L l TransStmt {} : _) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Transformative list comprehensions are not supported by the plugin")
  failIfErrsM
  return ([], False)
compileDo _ _ (L l RecStmt {} : _) =  do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Recursive do-notation is not supported by the plugin")
  failIfErrsM
  return ([], False)
compileDo ty ctxt (L _ (XStmtLR _) : ss) =
  compileDo ty ctxt ss

-- | Desugars pattern bindings in the given let-bindings.
-- This is done by introducing selector functions for each of them.
compileLet :: LHsLocalBinds GhcTc -> TcM [(RecFlag, LHsBinds GhcTc)]
compileLet (L _ (HsValBinds _ (XValBindsLR (NValBinds bs _)))) =
  mapM compileValBs bs
  where
    compileValBs (f, bs') = (f,) . listToBag
      <$> concatMapM compileLetBind (bagToList bs')
compileLet (L l (HsIPBinds _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Implicit parameters are not supported by the plugin")
  failIfErrsM
  return []
compileLet _                      = return []

-- | Desugars pattern bindings in the given let-binding.
-- This is done by introducing (multiple) selector functions
-- for the single binding.
compileLetBind :: LHsBindLR GhcTc GhcTc -> TcM [LHsBindLR GhcTc GhcTc]
compileLetBind (L l (AbsBinds x tvs evs ex ev bs sig)) = do
  bs' <- listToBag <$> concatMapM compileLetBind (bagToList bs)
  return [L l (AbsBinds x tvs evs ex ev bs' sig)]
compileLetBind (L _ (PatBind (NPatBindTc ns ty) p grhss _)) = do
  (b, fname) <- createOrdinaryFun
  (p', vs) <- prepareSelPat p
  let pe = noLoc (HsVar noExtField (noLoc fname))
  bs <- mapM (mkSelFun p' pe) vs
  return (b : bs)
  where
    -- create:
    -- fname = grhss
    createOrdinaryFun = do
      fname <- freshVar ty
      let ctxt = FunRhs (noLoc (varName fname)) Prefix NoSrcStrict
          alt = Match noExtField ctxt [] grhss
          mgtc = MatchGroupTc [] ty
          mg = MG mgtc (noLoc [noLoc alt]) Generated
      return (noLoc (FunBind ns (noLoc fname) mg WpHole []), fname)
    -- create:
    -- old = (\p' -> new) pe
    mkSelFun p' pe (old, new) = do
      let altLam = mkSimpleAlt LambdaExpr
            (noLoc (HsVar noExtField (noLoc new)))
              [removeOtherPatterns new p']
          mgtcLam = MatchGroupTc [ty] (varType new)
          mgLam = MG mgtcLam (noLoc [noLoc altLam]) Generated
      lam <- matchExpr (HsLam noExtField mgLam)
      let bdy = HsApp noExtField (noLoc (HsPar noExtField (noLoc lam))) pe
          grhs = GRHS noExtField [] (noLoc bdy)
          grhssSel = GRHSs noExtField [noLoc grhs]
            (noLoc (EmptyLocalBinds noExtField))
          ctxt = FunRhs (noLoc (varName old)) Prefix NoSrcStrict
          alt = Match noExtField ctxt [] grhssSel
          mgtc = MatchGroupTc [] (varType new)
          mg = MG mgtc (noLoc [noLoc alt]) Generated
      return (noLoc (FunBind ns (noLoc old) mg WpHole []))

    -- rename all variables in the pattern and remove all laziness in pattern
    prepareSelPat (L l1 p1) = first (L l1) <$> case p1 of
      VarPat x (L l2 v)   -> do v' <- freshVar (varType v)
                                return (VarPat x (L l2 v'), [(v,v')])
      LazyPat _ p2        -> first unLoc <$> prepareSelPat p2
      AsPat x (L l2 v) p2 -> do v' <- freshVar (varType v)
                                (p3, vs') <- prepareSelPat p2
                                return (AsPat x (L l2 v') p3, (v,v') : vs')
      ParPat _ p2         -> first unLoc <$> prepareSelPat p2
      BangPat x p2        -> first (BangPat x) <$> prepareSelPat p2
      ListPat x ps        -> do (ps', vss) <- unzip <$> mapM prepareSelPat ps
                                return (ListPat x ps', concat vss)
      TuplePat x ps b     -> do (ps', vss) <- unzip <$> mapM prepareSelPat ps
                                return (TuplePat x ps' b, concat vss)
      SumPat x p2 t b     -> first (\p3 -> SumPat x p3 t b) <$> prepareSelPat p2
      p2@ConPatOut{ pat_args = args } ->
        first (\args' -> p2 { pat_args = args'}) <$> prepareSelDetails args
      ViewPat x e p2 -> first (ViewPat x e) <$> prepareSelPat p2
      NPlusKPat x (L l2 v) lit1 lit2 se1 se2 -> do
        v' <- freshVar (varType v)
        return (NPlusKPat x (L l2 v') lit1 lit2 se1 se2, [(v,v')])
      SigPat x p2 ty' -> first (flip (SigPat x) ty') <$> prepareSelPat p2
      CoPat a b p2 c -> do (L _ p3, vs) <- prepareSelPat (noLoc p2)
                           return (CoPat a b p3 c, vs)
      p2             -> return (p2, [])

    prepareSelDetails (PrefixCon ps) = do
      (ps', vss) <- unzip <$> mapM prepareSelPat ps
      return (PrefixCon ps', concat vss)
    prepareSelDetails (RecCon (HsRecFields flds dd)) = do
      (flds', vss) <- unzip <$> mapM prepareSelField flds
      return (RecCon (HsRecFields flds' dd), concat vss)
    prepareSelDetails (InfixCon p1 p2) = do
      (p1', vs1) <- prepareSelPat p1
      (p2', vs2) <- prepareSelPat p2
      return (InfixCon p1' p2', vs1 ++ vs2)

    prepareSelField (L l1 (HsRecField v p1 pun)) =
      first (L l1 . flip (HsRecField v) pun) <$> prepareSelPat p1

    removeOtherPatterns :: Var -> LPat GhcTc -> LPat GhcTc
    removeOtherPatterns new p0@(L l1 p1) = L l1 $ case p1 of
      VarPat x (L l2 v)
        | v == new          -> VarPat x (L l2 v)
        | otherwise         -> WildPat (varType v)
      AsPat x (L l2 v) p2
        | v == new          -> VarPat x (L l2 v)
        | p2 `contains` new -> unLoc (removeOtherPatterns new p2)
        | otherwise         -> WildPat (varType v)
      BangPat x p2
        | p2 `contains` new -> BangPat x $ removeOtherPatterns new p2
      ListPat x ps
        | ps `contains` new -> ListPat x $ map (removeOtherPatterns new) ps
        | otherwise         -> WildPat (hsLPatType p0)
      TuplePat x ps b
        | ps `contains` new -> flip (TuplePat x) b $
                                 map (removeOtherPatterns new) ps
        | otherwise         -> WildPat (hsLPatType p0)
      SumPat x p2 t b
        | p2 `contains` new -> SumPat x (removeOtherPatterns new p2) t b
        | otherwise         -> WildPat (hsLPatType p0)
      p2@ConPatOut{ pat_args = args }
        | p2 `contains` new -> p2 { pat_args = removeOtherDetails new args }
        | otherwise         -> WildPat (hsLPatType p0)
      ViewPat x e p2
        | p2 `contains` new -> ViewPat x e $ removeOtherPatterns new p2
      NPlusKPat x (L l2 v) lit1 lit2 se1 se2
        | v == new          -> NPlusKPat x (L l2 v) lit1 lit2 se1 se2
        | otherwise         -> WildPat (hsLPatType p0)
      SigPat x p2 ty'       -> flip (SigPat x) ty' $ removeOtherPatterns new p2
      CoPat a b p2 c        -> CoPat a b
                                 (unLoc (removeOtherPatterns new (noLoc p2))) c
      _                     -> WildPat (hsLPatType p0)

    removeOtherDetails new (PrefixCon ps) =
      PrefixCon (map (removeOtherPatterns new) ps)
    removeOtherDetails new (RecCon (HsRecFields flds dd)) =
      RecCon (HsRecFields (map (removeOtherField new) flds) dd)
    removeOtherDetails new (InfixCon p1 p2) =
      InfixCon (removeOtherPatterns new p1) (removeOtherPatterns new p2)

    removeOtherField new (L l1 (HsRecField v p1 pun)) =
      L l1 (HsRecField v (removeOtherPatterns new p1) pun)
compileLetBind b = return [b]

-- | Checks if the first term contains the second term.
contains :: (Eq a, Data r, Typeable a) => r -> a -> Bool
contains r a = not (null (listify (==a) r))

-- | Compile a group of (case) alternatives into a more simple case without
-- any nested pattern matching.
compileMatchGroup :: MatchGroup GhcTc (LHsExpr GhcTc)
                  -> TcM (Either (MatchGroup GhcTc (LHsExpr GhcTc))
                                 (LHsExpr GhcTc))
compileMatchGroup (MG mgtc@(MatchGroupTc args res)
  (L _ alts@(L _ (Match _ ctxt@FunRhs {} _ _):_)) _)
  | null args        = do
    e <- errorExpr ctxt res >>= compileRhs alts
    let alt = mkSimpleAlt ctxt e []
    let mg = MG mgtc (noLoc [noLoc alt]) Generated
    return (Left mg)
compileMatchGroup mg@(MG (MatchGroupTc [_] _)
  (L _ (L _ (Match _ LambdaExpr [p] _):_)) _)
  | isVarPat p       = return (Left mg)
compileMatchGroup mg@(MG (MatchGroupTc _ res)
  (L _ (L _ (Match _ ctxt _ _):_)) _)
                     = errorExpr ctxt res >>= makeUnaryBindings ctxt [] mg
compileMatchGroup mg = return (Left mg)

-- | Transform any multi-arity match group
-- into multiple lambdas and case expressions
makeUnaryBindings :: HsMatchContext Name -> [Var]
                  -> MatchGroup GhcTc (LHsExpr GhcTc) -> LHsExpr GhcTc
                  -> TcM (Either (MatchGroup GhcTc (LHsExpr GhcTc))
                                 (LHsExpr GhcTc))
makeUnaryBindings ctxt vs (MG (MatchGroupTc args res) (L l alts) _) e =
  case args of
    []   -> let vs' = reverse vs
            in Right <$> compileMatching vs' res alts e
    x:xs -> do
      v <- freshVar x
      let remaining = MG (MatchGroupTc xs res) (L l alts) Generated
      exOrMG <- makeUnaryBindings LambdaExpr (v:vs) remaining e
      let bdy1 = case exOrMG of
            Left  mg -> noLoc (HsLam noExtField mg)
            Right ex -> ex

      let mgtcLam = MatchGroupTc [x] (foldr mkVisFunTy res xs)
      let patLam = VarPat noExtField (noLoc v)
      let innerCtxt = if isFunCtxt ctxt then LambdaExpr else ctxt
      let altLam = mkSimpleAlt innerCtxt bdy1 [noLoc patLam]
      let mgLam = MG mgtcLam (noLoc [noLoc altLam]) Generated

      if isFunCtxt ctxt
        then do
          let mgtcTop = MatchGroupTc [] (foldr mkVisFunTy res args)
          let bdy2 = HsLam noExtField mgLam
          let altTop = mkSimpleAlt ctxt (noLoc bdy2) []
          let mgTop = MG mgtcTop (noLoc [noLoc altTop]) Generated
          return (Left mgTop)
        else
          return (Left mgLam)
makeUnaryBindings _ _ x _  = return (Left x)

-- | Compile all matchings of a specific match group to nested cases.
compileMatching :: [Var] -> Type -> [LMatch GhcTc (LHsExpr GhcTc)]
                -> LHsExpr GhcTc
                -> TcM (LHsExpr GhcTc)
compileMatching [] _  eqs err = compileRhs eqs err
compileMatching vs ty eqs err = matchOn 0 vs ty eqs err

-- | Compile local bindings and guards of a rhs.
compileRhs :: [LMatch GhcTc (LHsExpr GhcTc)] -> LHsExpr GhcTc
           -> TcM (LHsExpr GhcTc)
compileRhs (L _ (Match _ _ _ (GRHSs _ grhs lcl)):xs) err = do
  err' <- compileRhs xs err
  mkLocalBinds lcl <$> foldM compileGuard err' (reverse grhs)
compileRhs _ err = return err

-- | Compile a single guard alternative.
compileGuard :: LHsExpr GhcTc -> LGRHS GhcTc (LHsExpr GhcTc)
             -> TcM (LHsExpr GhcTc)
compileGuard err (L _ (GRHS _ stmts e)) =
  foldM (compileGuardStmt err) e (reverse stmts)
compileGuard err (L _ (XGRHS _)) = return err

-- | Compile a single statement from a guard.
compileGuardStmt :: LHsExpr GhcTc -> LHsExpr GhcTc -> GuardLStmt GhcTc
                 -> TcM (LHsExpr GhcTc)
compileGuardStmt err e (L _ (BindStmt resty p (L _ (HsVar _ (L _ v))) _ _)) = do
  let alt = mkSimpleAlt CaseAlt e [p]
  compileMatching [v] resty [noLoc alt] err
compileGuardStmt err e (L _ (BindStmt resty p g _ _)) = do
  let alt = mkSimpleAlt CaseAlt e [p]
  ty <- getTypeOrPanic g
  v <- freshVar ty
  e' <- compileMatching [v] resty [noLoc alt] err
  return (noLoc (mkSimpleLet Recursive g e' v ty))
compileGuardStmt err e (L _ (BodyStmt _   g _ _)) =
  return (noLoc (HsIf noExtField Nothing g e err))
compileGuardStmt _   e (L _ (LetStmt  _ b      )) =
  return (noLoc (HsLet noExtField b e))
compileGuardStmt _   _ s =
  panicAny "Unexpected statement in guard" s

mkLocalBinds :: LHsLocalBinds GhcTc -> LHsExpr GhcTc -> LHsExpr GhcTc
mkLocalBinds (L _ (EmptyLocalBinds _)) e = e
mkLocalBinds b                         e = noLoc (HsLet noExtField b e)

matchOn :: Int -> [Var] -> Type -> [LMatch GhcTc (LHsExpr GhcTc)]
        -> LHsExpr GhcTc
        -> TcM (LHsExpr GhcTc)
matchOn n vs ty eqs err = do
  let pms = map (getPatternAt n) eqs
  let pmss = groupBy (\a -> isSamePatternType (fst a) . fst) pms
  foldM (matchOnSame n vs ty) err (reverse pmss)

matchOnSame :: Int -> [Var] -> Type -> LHsExpr GhcTc
            -> [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))]
            -> TcM (LHsExpr GhcTc)
matchOnSame n vs ty err eqs
  | isVar     = mkVarMatch   n vs ty err eqs
  | isConstr  = mkConMatch   n vs ty err eqs
  | otherwise = mkOtherMatch n vs ty err eqs
  where
    isVar    = isVarPat (fst (head eqs))
    isConstr = isConstrPat (fst (head eqs))

mkVarMatch :: Int -> [Var] -> Type -> LHsExpr GhcTc
           -> [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))]
           -> TcM (LHsExpr GhcTc)
mkVarMatch n vs ty err eqs = do
  let (v, vs') = getAndDrop n vs
  let noAs = map (preprocessAs v) eqs
  alts <- mapM (bindVarAlt v) noAs
  e <- compileMatching vs' ty alts err
  if any (isBangPat . fst) noAs
    then mkSeq v e
    else return e

-- HACK: since Int# is "invisible" to the lifting and any I# constructor for Int is removed, 
-- this function has to see through any I# constructor
bindVarAlt :: Var -> (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
           -> TcM (LMatch GhcTc (LHsExpr GhcTc))
bindVarAlt v (L _ (VarPat _ (L _ v')), m) = return (substitute v v' m)
bindVarAlt _ (L _ (WildPat _    ), m) = return m
bindVarAlt v (L _ (BangPat _ p  ), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (LazyPat _ p  ), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (ParPat _ p   ), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (SigPat _ p _ ), m) = bindVarAlt v (p, m)
bindVarAlt v (L _ (CoPat _ _ p _), m) = bindVarAlt v (noLoc p, m)
bindVarAlt v (L _ p@ConPatOut {} , m) 
  | L _ (RealDataCon c) <- pat_con p
  , c == intDataCon
  , [arg] <- hsConPatArgs (pat_args p) = 
      bindVarAlt v (arg, m)
bindVarAlt _ (_,m) = return m

mkSeq :: Var -> LHsExpr GhcTc -> TcM (LHsExpr GhcTc)
mkSeq _ e = do
  flags <- getDynFlags
  reportError (mkErrMsg flags noSrcSpan neverQualify
    "Bang patterns are not supported by the plugin")
  failIfErrsM
  return e

mkOtherMatch :: Int -> [Var] -> Type -> LHsExpr GhcTc
             -> [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))]
             -> TcM (LHsExpr GhcTc)
mkOtherMatch _ _ _ _ [] =
  panicAny "Unexpected empty list of rules" ()
mkOtherMatch _ _ _ e ((L l _, _):_) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Pattern match extensions are not supported by the plugin")
  failIfErrsM
  return e

mkConMatch :: Int -> [Var] -> Type -> LHsExpr GhcTc
           -> [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))]
           -> TcM (LHsExpr GhcTc)
mkConMatch n vs ty2 err eqs = do
  let (v,vs') = getAndDrop n vs
  let ty1 = varType v
  let noAs = map (preprocessAs v) eqs
  alts <- mkAlts v vs' ty1 ty2 err noAs
  case alts of
    Left as -> let mgtc = MatchGroupTc [ty1] ty2
                   mg = MG mgtc (noLoc as) Generated
                   e = HsCase noExtField (noLoc (HsVar noExtField (noLoc v))) mg
               in return (noLoc e)
    Right e -> return e

-- This can Either return a List of matches if the top pattern is not lazy,
-- or if it is lazy, we return the expression to be used instead.
mkAlts :: Var -> [Var] -> Type -> Type -> LHsExpr GhcTc
       -> [(LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))]
       -> TcM (Either [LMatch GhcTc (LHsExpr GhcTc)] (LHsExpr GhcTc))
mkAlts v vs ty1 ty2 err eqs@((p, alt) : _)
  | L _ c@ConPatOut {} <- p,
    L _ (RealDataCon dc) <- pat_con c,
    isNewTyCon (dataConTyCon dc) = do
      (p', [v'], _) <- flattenPat p
      let patTy = hsLPatType p'
      let xty = varType v'
      x <- freshVar xty
      fresh <- freshVar patTy
      -- create: let x = (\a -> case a of p' -> v') v in rhs
      let grhs = GRHS noExtField [] (noLoc (HsVar noExtField (noLoc v')))
          rhs = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
          match = Match noExtField CaseAlt [p'] rhs
          mgtc = MatchGroupTc [patTy] (varType v')
          mg = MG mgtc (noLoc [noLoc match]) Generated
          cse = noLoc (HsCase noExtField (noLoc (HsVar noExtField (noLoc fresh))) mg)
          lam = mkLam (noLoc fresh) patTy cse (varType v')
          lamApp = mkHsApp lam (noLoc (HsVar noExtField (noLoc v)))

      eqs' <- mapM flattenEq [(p, alt)]
      bdy <- compileMatching (x : vs) ty2 eqs' err
      return $ Right $ noLoc $ mkSimpleLet NonRecursive lamApp bdy x (varType x)
  | otherwise = do
    -- Assuming the first pattern is not a lazy pattern,
    -- we need every alternative with the same constructor as the first one
    -- If that is already a lazy pattern, it is assumed to be matching.
    -- A lazy pattern gets desugared to a let-bound pattern, which then gets
    -- desugared to selector functions
    let (strict, rest) = span (isNoLazyPat . fst) eqs
    let (with, without) = partition (sameTopCon p . fst) strict
    if isNoLazyPat p
      then do
        (p', vs',_) <- flattenPat p
        alts' <- mkAlts v vs ty1 ty2 err (rest ++ without)
        eqs' <- mapM flattenEq with
        bdy <- compileMatching (vs' ++ vs) ty2 eqs' err
        mkNaturalOrSimpleAlt ty1 ty2 v bdy p' alts'
      else do
        -- compile any remaining patterns
        bdy <- compileMatching vs ty2 [alt] err
        -- construct new pattern binding and translate that
        let vE = noLoc (HsVar noExtField (noLoc v))
        letExpr <- matchExpr (mkSimplePatLet ty1 vE p bdy)
        -- return just this expression to be either placed
        -- in a new wildcard branch, or to completely replace the case,
        -- iff it is the first alternative.
        -- All remaining patterns would be overlapping, so we ignore them
        return (Right (noLoc letExpr))
mkAlts _ _  ty1 _ err   [] =
  let grhs = GRHS noExtField [] err
      grhss = GRHSs noExtField [noLoc grhs] (noLoc (EmptyLocalBinds noExtField))
      alt = Match noExtField CaseAlt [noLoc (WildPat ty1)] grhss
  in return (Left [noLoc alt])

-- Desugars natural patterns (e.g. overloaded literals)
-- and string patterns into if-then-else.
-- Any other pattern is translated into a normal case-expression
mkNaturalOrSimpleAlt :: Type -> Type -> Var -> LHsExpr GhcTc -> LPat GhcTc
                     -> Either [LMatch GhcTc (LHsExpr GhcTc)] (LHsExpr GhcTc)
                     -> TcM (Either [LMatch GhcTc (LHsExpr GhcTc)] (LHsExpr GhcTc))
mkNaturalOrSimpleAlt ty1 ty2 v e1 (L l (LitPat _ lit)) alts
  | isCharLit lit = do
    let c = litChar lit
    x <- liftQ [| eqChar c |] >>= flip mkNewAny (mkVisFunTys [charTy] boolTy)
    let ve = HsVar noExtField (noLoc v)
        if1 = mkHsApp x (noLoc ve)
        if2 = e1
        if3 = case alts of
                Left as ->
                  let mgtc = MatchGroupTc [ty1] ty2
                      mg = MG mgtc (noLoc as) Generated
                  in noLoc (HsCase noExtField (noLoc ve) mg)
                Right e2 -> e2
    return (Right (noLoc (HsIf noExtField Nothing if1 if2 if3)))
  | isStringLit lit =
    mkNaturalOrSimpleAlt ty1 ty2 v e1 (L l (NPat
      strTy
      (L l (OverLit
        (OverLitTc False strTy)
        (HsIsString (stringLitSourceText lit) (stringLitFastString lit))
        (HsLit noExtField lit)))
      Nothing
      (SyntaxExpr
        (HsVar noExtField (noLoc (mkGlobalVar
           VanillaId eqStringName
           (mkVisFunTy strTy (mkVisFunTy strTy boolTy))
           vanillaIdInfo)))
        [WpHole, WpHole]
        WpHole))) alts
  where strTy = mkTyConApp listTyCon [mkTyConTy charTyCon]
mkNaturalOrSimpleAlt ty1 ty2 v e1 (L _ (NPat _ (L _ (OverLit _ _ l)) neg
  (SyntaxExpr eq [argWQ1, argWQ2] resWQ))) alts =
  let ve = HsVar noExtField (noLoc v)
      l' = case neg of
             Just (SyntaxExpr en [argWN] resWN) ->
               HsWrap noExtField resWN (HsApp noExtField (noLoc en)
                                          (noLoc (HsWrap noExtField argWN l)))
             _ -> l
      if1 = noLoc (HsWrap noExtField resWQ
              (HsApp noExtField (noLoc (HsApp noExtField
                (noLoc eq)
                (noLoc (HsWrap noExtField argWQ1 l'))))
                (noLoc (HsWrap noExtField argWQ2 ve))))
      if2 = e1
      if3 = case alts of
              Left as ->
                let mgtc = MatchGroupTc [ty1] ty2
                    mg = MG mgtc (noLoc as) Generated
                in noLoc (HsCase noExtField (noLoc ve) mg)
              Right e2 -> e2
  in return $ Right (noLoc (HsIf noExtField Nothing if1 if2 if3))
mkNaturalOrSimpleAlt _ _ _ e1 p (Left as) =
  return $ Left (noLoc (mkSimpleAlt CaseAlt e1 [p]) : as)
mkNaturalOrSimpleAlt ty1 _ _ e1 p (Right e2) =
  return $ Left [ noLoc (mkSimpleAlt CaseAlt e1 [p])
                , noLoc (mkSimpleAlt CaseAlt e2 [noLoc (WildPat ty1)])]

-- HACK: since Int# is "invisible" to the lifting and any I# constructor for Int is removed, 
-- this function has to see through any I# constructor
preprocessAs :: Var -> (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
             -> (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
preprocessAs v (L _ (AsPat _ (L _ v') p), m) =
  let m' = substitute v v' m
  in preprocessAs v (p, m')
preprocessAs v (L l (LazyPat x p), m) =
  first (L l . LazyPat x) (preprocessAs v (p, m))
preprocessAs v (L l (BangPat x p), m) =
  first (L l . BangPat x) (preprocessAs v (p, m))
preprocessAs v (L l (SigPat x p ty), m) =
  first (L l . flip (SigPat x) ty) (preprocessAs v (p, m))
preprocessAs v (L _ (ParPat _ p), m) =
  preprocessAs v (p, m)
preprocessAs v (L _ p@ConPatOut {}, m)
  | L _ (RealDataCon c) <- pat_con p
  , c == intDataCon
  , [arg] <- hsConPatArgs (pat_args p) = 
    preprocessAs v (arg, m)
preprocessAs _ (p, m) = (p, m)

flattenEq :: (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
          -> TcM (LMatch GhcTc (LHsExpr GhcTc))
flattenEq (p, L l (Match a b ps c)) = do
  (_,_,ps') <- flattenPat p
  return (L l (Match a b (ps' ++ ps) c))
flattenEq (_,b) = return b

-- Flatten a pattern into the top constructor pattern
-- and the sub-patterns with their new variables
flattenPat :: LPat GhcTc -> TcM (LPat GhcTc, [Var], [LPat GhcTc])
flattenPat p@(L _ (WildPat _  )) = return (p, [], [])
flattenPat p@(L _ (VarPat _ _ )) = return (p, [], [])
flattenPat (L l (LazyPat x p  )) =
  (\(a,b,c) -> (L l (LazyPat x a), b, c)) <$> flattenPat p
flattenPat (L l (AsPat x v p  )) =
  (\(a,b,c) -> (L l (AsPat x v a), b, c)) <$> flattenPat p
flattenPat (L l (ParPat x p   )) =
  (\(a,b,c) -> (L l (ParPat x a), b, c)) <$> flattenPat p
flattenPat (L l (BangPat x p  )) =
   (\(a,b,c) -> (L l (BangPat x a), b, c)) <$> flattenPat p
flattenPat p@(L l (ListPat (ListPatTc _ (Just _)) _ )) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Overloaded lists are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
flattenPat (L l (ListPat (ListPatTc ty Nothing) [] )) = do
  let dc = noLoc (RealDataCon nilDataCon)
  let res = L l (ConPatOut dc [ty] [] [] (EvBinds emptyBag) (PrefixCon []) WpHole)
  return (res, [], [])
flattenPat (L l (ListPat tc@(ListPatTc ty Nothing) (x:xs))) = do
  v1 <- mkVar ty
  v2 <- mkVar (mkTyConApp listTyCon [ty])
  let dc = noLoc (RealDataCon consDataCon)
  let c  = PrefixCon [ noLoc (VarPat noExtField (noLoc v1))
                     , noLoc (VarPat noExtField (noLoc v2))]
  let res = L l (ConPatOut dc [ty] [] [] (EvBinds emptyBag) c WpHole)
  return (res, [v1, v2], [x, noLoc (ListPat tc xs)])
flattenPat (L l (TuplePat tys ps b)) =
  (\vs -> (L l (TuplePat tys (map mkVarPat vs) b), vs, ps))
  <$> mapM mkVar tys
flattenPat (L l (SumPat tys p t a)) =
  (\v -> (L l (SumPat tys (noLoc (VarPat noExtField (noLoc v))) t a), [v], [p]))
  <$> mkVar (tys !! t)
flattenPat p@(L _ (ConPatIn _ _)) =
  panicAny "Untyped pattern not expected after TC" p
flattenPat (L l cn@ConPatOut{}) =
  let argtys = pat_arg_tys cn
      cty = conLikeInstOrigArgTys (unLoc (pat_con cn)) argtys
  in (\(args', vs, c) -> (L l (cn { pat_args = args' }), vs, c))
       <$> flattenConPatDetails (pat_args cn) cty argtys
flattenPat p@(L l ViewPat {}) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "View pattern are not supported by the plugin")
  failIfErrsM
  return (p, [], [])
flattenPat p@(L l (SplicePat _ _)) = do
  flags <- getDynFlags
  reportError (mkErrMsg flags l neverQualify
    "Template Haskell is not supported by the plugin")
  failIfErrsM
  return (p, [], [])
flattenPat p@(L _ (LitPat _ _ )) = return (p, [], [])
flattenPat p@(L _ NPat {}) = return (p, [], [])
flattenPat p@(L _ NPlusKPat {}) =  return (p, [], [])
flattenPat (L l (SigPat x p ty)) =
  (\(a,b,c) -> (L l (SigPat x a ty), b, c)) <$> flattenPat p
flattenPat (L l (CoPat x co p w)) =
  (\(a,b,c) -> (L l (CoPat x co (unLoc a) w), b, c)) <$> flattenPat (noLoc p)
flattenPat p@(L _ (XPat _)) = return (p, [], [])

flattenConPatDetails :: HsConPatDetails GhcTc -> [Type] -> [Type]
                     -> TcM (HsConPatDetails GhcTc, [Var], [LPat GhcTc])
flattenConPatDetails (PrefixCon args) tys _ = do
  vs <- mapM mkVar tys
  return (PrefixCon (map (noLoc . VarPat noExtField . noLoc ) vs), vs, args)
flattenConPatDetails (RecCon (HsRecFields flds d)) _ tys = do
  (flds', vs, args) <- unzip3 <$> mapM (flattenRecField tys) flds
  return (RecCon (HsRecFields flds' d), concat vs, concat args)
flattenConPatDetails (InfixCon a1 a2) tys _ = do
  [v1, v2] <- mapM mkVar tys
  let p1 = mkVarPat v1
  let p2 = mkVarPat v2
  return (InfixCon p1 p2, [v1,v2], [a1,a2])

flattenRecField :: [Type] -> LHsRecField GhcTc (LPat GhcTc)
                -> TcM (LHsRecField GhcTc (LPat GhcTc), [Var], [LPat GhcTc])
flattenRecField tys (L l (HsRecField idt p pn)) = do
  let ty = funResultTy (instantiateWith tys (varType (extFieldOcc (unLoc idt))))
  v <- mkVar ty
  let p' = noLoc (VarPat noExtField (noLoc v))
  return (L l (HsRecField idt p' pn), [v], [p])

mkVar :: Type -> TcM Var
mkVar ty =
  (\u -> mkLocalVar VanillaId (mkSystemName u (mkVarOcc "p")) ty vanillaIdInfo)
  <$> getUniqueM

substitute :: Data a => Var -> Var -> a -> a
substitute new old = everywhere (mkT substVar)
 where
    u = varName old
    substVar v = if varName v == u then new else v

getPatternAt :: Int -> LMatch GhcTc (LHsExpr GhcTc)
             -> (LPat GhcTc, LMatch GhcTc (LHsExpr GhcTc))
getPatternAt n (L l (Match x c ps lcl)) =
  let (p, rs) = getAndDrop n ps
  in (p, L l (Match x c rs lcl))
getPatternAt _ _ = panicAnyUnsafe "No pattern at the specified index" ()

getAndDrop :: Int -> [a] -> (a, [a])
getAndDrop _ []     = panicAnyUnsafe "No pattern at the specified index" ()
getAndDrop 0 (x:xs) = (x,xs)
getAndDrop n (x:xs) =
  let (y,ys) = getAndDrop (n-1) xs
  in (y, x:ys)

isSamePatternType :: LPat GhcTc -> LPat GhcTc -> Bool
isSamePatternType p1 p2 = isConstrPat p1 && isConstrPat p2
  || isVarPat p1 && isVarPat p2

isConstrPat :: LPat GhcTc -> Bool
isConstrPat (L _ (WildPat _    )) = False
isConstrPat (L _ (VarPat _ _   )) = False
isConstrPat (L _ (LazyPat _ p  )) = isConstrPat p
isConstrPat (L _ (AsPat _ _ p  )) = isConstrPat p
isConstrPat (L _ (ParPat _ p   )) = isConstrPat p
isConstrPat (L _ (BangPat _ p  )) = isConstrPat p
isConstrPat (L _ (ListPat _ _  )) = True
isConstrPat (L _ TuplePat {}    ) = True
isConstrPat (L _ SumPat {}      ) = True
isConstrPat (L _ (ConPatIn _ _ )) = True
isConstrPat (L _ ConPatOut{}    ) = True
isConstrPat (L _ ViewPat{}      ) = False
isConstrPat (L _ (SplicePat _ _)) = False
isConstrPat (L _ (LitPat _ _   )) = True
isConstrPat (L _ NPat{}         ) = True
isConstrPat (L _ NPlusKPat{}    ) = False
isConstrPat (L _ (SigPat _ p _ )) = isConstrPat p
isConstrPat (L _ (CoPat _ _ p _)) = isConstrPat (noLoc p)
isConstrPat (L _ (XPat _       )) = False

-- HACK: since Int# is "invisible" to the lifting and any I# constructor for Int is removed, 
-- this function has to see through any I# constructor
isVarPat :: LPat GhcTc -> Bool
isVarPat (L _ (WildPat _    )) = True
isVarPat (L _ (VarPat _ _   )) = True
isVarPat (L _ (LazyPat _ p  )) = isVarPat p
isVarPat (L _ (AsPat _ _ p  )) = isVarPat p
isVarPat (L _ (ParPat _ p   )) = isVarPat p
isVarPat (L _ (BangPat _ p  )) = isVarPat p
isVarPat (L _ (ListPat _ _  )) = False
isVarPat (L _ TuplePat {}    ) = False
isVarPat (L _ SumPat {}      ) = False
isVarPat (L _ (ConPatIn _ _ )) = False
isVarPat (L _ p@ConPatOut{}    ) 
  | L _ (RealDataCon c) <- pat_con p
  , c == intDataCon
  , [arg] <- hsConPatArgs (pat_args p) 
                               = isVarPat arg
  | otherwise                  = False
isVarPat (L _ ViewPat{}      ) = False
isVarPat (L _ (SplicePat _ _)) = False
isVarPat (L _ (LitPat _ _   )) = False
isVarPat (L _ NPat{}         ) = False
isVarPat (L _ NPlusKPat{}    ) = False
isVarPat (L _ (SigPat _ p _ )) = isVarPat p
isVarPat (L _ (CoPat _ _ p _)) = isVarPat (noLoc p)
isVarPat (L _ (XPat _       )) = False

isBangPat :: LPat GhcTc -> Bool
isBangPat (L _ (WildPat _    )) = False
isBangPat (L _ (VarPat _ _   )) = False
isBangPat (L _ (LazyPat _ p  )) = isBangPat p
isBangPat (L _ (AsPat _ _ p  )) = isBangPat p
isBangPat (L _ (ParPat _ p   )) = isBangPat p
isBangPat (L _ (BangPat _ _  )) = True
isBangPat (L _ (ListPat _ _  )) = False
isBangPat (L _ TuplePat {}    ) = False
isBangPat (L _ SumPat {}      ) = False
isBangPat (L _ (ConPatIn _ _ )) = False
isBangPat (L _ ConPatOut{}    ) = False
isBangPat (L _ ViewPat{}      ) = False
isBangPat (L _ (SplicePat _ _)) = False
isBangPat (L _ (LitPat _ _   )) = False
isBangPat (L _ NPat{}         ) = False
isBangPat (L _ NPlusKPat{}    ) = False
isBangPat (L _ (SigPat _ p _ )) = isBangPat p
isBangPat (L _ (CoPat _ _ p _)) = isBangPat (noLoc p)
isBangPat (L _ (XPat _       )) = False

isNoLazyPat :: LPat GhcTc -> Bool
isNoLazyPat (L _ (WildPat _    )) = True
isNoLazyPat (L _ (VarPat _ _   )) = True
isNoLazyPat (L _ (LazyPat _ _  )) = False
isNoLazyPat (L _ (AsPat _ _ p  )) = isNoLazyPat p
isNoLazyPat (L _ (ParPat _ p   )) = isNoLazyPat p
isNoLazyPat (L _ (BangPat _ p  )) = isNoLazyPat p
isNoLazyPat (L _ (ListPat _ _  )) = True
isNoLazyPat (L _ TuplePat {}    ) = True
isNoLazyPat (L _ SumPat {}      ) = True
isNoLazyPat (L _ (ConPatIn _ _ )) = True
isNoLazyPat (L _ ConPatOut{}    ) = True
isNoLazyPat (L _ ViewPat{}      ) = True
isNoLazyPat (L _ (SplicePat _ _)) = True
isNoLazyPat (L _ (LitPat _ _   )) = True
isNoLazyPat (L _ NPat{}         ) = True
isNoLazyPat (L _ NPlusKPat{}    ) = True
isNoLazyPat (L _ (SigPat _ p _ )) = isNoLazyPat p
isNoLazyPat (L _ (CoPat _ _ p _)) = isNoLazyPat (noLoc p)
isNoLazyPat (L _ (XPat _       )) = True

-- this is more delicate than it seems,
-- as we have to make sure that ListPat and TuplePat are "the same" as their
-- explicit constructors
sameTopCon :: LPat GhcTc -> LPat GhcTc -> Bool
sameTopCon (L _ (WildPat _    )) (L _ (WildPat _    ))  = True
sameTopCon (L _ (VarPat _ _   )) (L _ (VarPat _ _   ))  = True
sameTopCon (L _ (LazyPat _ _  )) (L _ (LazyPat _ _  ))  = True
sameTopCon (L _ AsPat {}       ) (L _ AsPat {}       )  = True
sameTopCon (L _ (ParPat _ p1  )) p2                     = sameTopCon p1 p2
sameTopCon p1                    (L _ (ParPat _ p2  ))  = sameTopCon p1 p2
sameTopCon (L _ (BangPat _ _  )) (L _ (BangPat _ _  ))  = True
sameTopCon (L _ (ListPat _ ps1)) (L _ (ListPat _ ps2))  = null ps1 == null ps2
sameTopCon (L _ (ListPat _ ps1))
           (L _ ConPatOut
             { pat_con = L _ (RealDataCon c) })         = null ps1 ==
                                                          (c == nilDataCon)
sameTopCon (L _ ConPatOut { pat_con = L _ (RealDataCon c) })
           (L _ (ListPat _ ps1))                        = null ps1 ==
                                                          (c == nilDataCon)
sameTopCon (L _ TuplePat {}    ) (L _ TuplePat {}    )  = True
sameTopCon (L _ (TuplePat _ ps b))
           (L _ ConPatOut
             { pat_con = L _ (RealDataCon c) })         = c == tc
  where tc = tupleDataCon b (length ps)
sameTopCon (L _ ConPatOut
             { pat_con = L _ (RealDataCon c) })
           (L _ (TuplePat _ ps b))                      = c == tc
    where tc = tupleDataCon b (length ps)
sameTopCon (L _ (SumPat _ _ t1 _))
           (L _ (SumPat _ _ t2 _))                      = t1 == t2
sameTopCon (L _ (ConPatIn v1 _)) (L _ (ConPatIn v2 _))  = v1 == v2
sameTopCon (L _ (ConPatOut (L _ c1) _ _ _ _ _ _))
           (L _ (ConPatOut (L _ c2) _ _ _ _ _ _))       = sameConLike c1 c2
sameTopCon (L _ ViewPat{}      ) (L _ ViewPat{}      )  = False
sameTopCon (L _ (SplicePat _ _)) (L _ (SplicePat _ _))  = False
sameTopCon (L _ (LitPat _ l1  )) (L _ (LitPat _ l2  ))  = l1 == l2
sameTopCon (L _ (NPat _ (L _ l1) _ _ ))
           (L _ (NPat _ (L _ l2) _ _ ))                 = l1 == l2
sameTopCon (L _ (NPlusKPat _ _ (L _ l1) _ _ _))
           (L _ (NPlusKPat _ _ (L _ l2) _ _ _))         = l1 == l2
sameTopCon (L _ (SigPat _ p1 _)) p2                     = sameTopCon p1 p2
sameTopCon p1                    (L _ (SigPat _ p2 _))  = sameTopCon p1 p2
sameTopCon p1                    (L _ (CoPat _ _ p2 _)) = sameTopCon p1 p2'
  where p2' = noLoc p2
sameTopCon (L _ (CoPat _ _ p1 _)) p2                    = sameTopCon p1' p2
  where p1' = noLoc p1
sameTopCon _ _ = False

sameConLike :: ConLike -> ConLike -> Bool
sameConLike (RealDataCon c1) (RealDataCon c2) = dataConName c1 == dataConName c2
sameConLike (PatSynCon   c1) (PatSynCon   c2) = patSynName  c1 == patSynName  c2
sameConLike _ _ = False

isFunCtxt :: HsMatchContext Name -> Bool
isFunCtxt FunRhs {} = True
isFunCtxt _         = False

errorExpr :: HsMatchContext Name -> Type -> TcM (LHsExpr GhcTc)
errorExpr (FunRhs (L _ idt) _ _) ty =
  mkErrorWith ty $ "Non-exhaustive patterns in function: " ++
    occNameString (occName idt)
errorExpr LambdaExpr ty =
  mkErrorWith ty "Non-exhaustive patterns in lambda abstraction"
errorExpr CaseAlt ty =
  mkErrorWith ty "Non-exhaustive patterns in case expression"
errorExpr IfAlt ty =
  mkErrorWith ty "Non-exhaustive guard alternatives in multi-way if"
errorExpr ProcExpr ty =
  mkErrorWith ty "Non-exhaustive patterns in a proc expression"
errorExpr PatBindRhs ty =
  mkErrorWith ty "Non-exhaustive patterns in a pattern binding"
errorExpr PatBindGuards ty =
  mkErrorWith ty "Non-exhaustive guard alternatives in a pattern binding"
errorExpr (StmtCtxt _) ty =
  mkErrorWith ty "Non-exhaustive patterns in a list comprehension or do-notation"
errorExpr ThPatSplice ty =
  mkErrorWith ty "Non-exhaustive patterns in a TemplateHaskell pattern splice "
errorExpr ThPatQuote ty =
  mkErrorWith ty "Non-exhaustive patterns in a TemplateHaskell pattern quotation"
errorExpr PatSyn ty =
  mkErrorWith ty "Non-exhaustive patterns in a pattern synonym declaration"
errorExpr RecUpd _ =
  panicAny "Unexpected RecUpd context of a pattern matching" ()
  -- Introduced in dsExpr only

errorStrStmt :: HsStmtContext Name -> LHsExpr GhcTc
errorStrStmt ListComp =
  mkErrorLit "Non-exhaustive patterns in a List comprehension"
errorStrStmt MonadComp =
  mkErrorLit "Non-exhaustive patterns in a Monad comprehension"
errorStrStmt DoExpr =
  mkErrorLit "Non-exhaustive patterns in a do expression"
errorStrStmt MDoExpr =
  mkErrorLit "Non-exhaustive patterns in a recursive do expression"
errorStrStmt ArrowExpr =
  mkErrorLit "Non-exhaustive patterns in an arrow expression"
errorStrStmt GhciStmtCtxt =
  mkErrorLit "Non-exhaustive patterns in a GHCi statement"
errorStrStmt (PatGuard _) =
  panicAnyUnsafe "Unexpected pattern guard context in do-notation" ()
errorStrStmt (ParStmtCtxt _) =
  mkErrorLit "Non-exhaustive patterns in a branch of a parallel do statement"
errorStrStmt (TransStmtCtxt _) =
  mkErrorLit "Non-exhaustive patterns in a branch of a transform statement"

mkErrorLit :: String -> LHsExpr GhcTc
mkErrorLit = noLoc . HsLit noExtField . HsString NoSourceText . mkFastString

mkErrorWith :: Type -> String -> TcM (LHsExpr GhcTc)
mkErrorWith ty s = do
  hscEnv <- getTopEnv
  Found _ mdl <- liftIO $
    findImportedModule hscEnv (mkModuleName "Plugin.BuiltIn") Nothing
  errId <- lookupId =<< lookupOrig mdl ( mkVarOcc "failFLStr" )
  errId' <- setVarName errId <$> externaliseName mdl (varName errId)
  return (noLoc (HsApp noExtField
    (noLoc (HsWrap noExtField (WpTyApp ty) (HsVar noExtField (noLoc errId'))))
    (mkErrorLit s)))
