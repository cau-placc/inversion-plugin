{-# LANGUAGE TemplateHaskell #-}
module Plugin.NLPlugin where

import Plugins
import GhcPlugins
import GHC.Hs
import GHC.ThToHs
import Bag

import Language.Haskell.TH hiding (Match, ValD, FunD, SigD)
import qualified Language.Haskell.TH as TH
import Control.Monad.State
import Plugin.Effect.Monad
import Plugin.Effect.Util
import Plugin.Effect.TH
import Plugin.Trans.Util
import Plugin.BuiltIn (Tuple2FL(..))
import Data.List.Extra
import Plugin.Effect.TH

import Data.Maybe
import Data.Either

plugin :: Plugin
plugin = defaultPlugin
  { parsedResultAction    = transNLPatternPlugin
  }

transNLPatternPlugin :: [CommandLineOption] -> ModSummary -> HsParsedModule -> Hsc HsParsedModule
transNLPatternPlugin _ summary mdl@(HsParsedModule (L loc hsmdl) _ _) = do
  let ds = hsmodDecls hsmdl
  ds' <- mapM (\(L l d) -> L l <$> transNLPatternDecl d) ds

  let hsmdl' = hsmdl { hsmodDecls = ds' }
  return mdl { hpm_module = L loc hsmdl'}

transNLPatternDecl :: HsDecl GhcPs -> Hsc (HsDecl GhcPs)
transNLPatternDecl (ValD _ f@(FunBind _ _ mg _ _)) = do
  mg' <- transNLPatternMG mg
  return (ValD noExtField (f { fun_matches = mg' }))
transNLPatternDecl (InstD _ _) = undefined
transNLPatternDecl d = return d

transNLPatternMG :: MatchGroup GhcPs (LHsExpr GhcPs) -> Hsc (MatchGroup GhcPs (LHsExpr GhcPs))
transNLPatternMG mg@(MG _ (L l eqs) _) = do
  eqs' <- mapM (\(L l' e) -> L l' <$> transNLPatternEq e) eqs
  return (mg { mg_alts = L l eqs' })

type NLTransM = StateT (Integer, [RdrName]) Hsc

transNLPatternEq :: Match GhcPs (LHsExpr GhcPs) -> Hsc (Match GhcPs (LHsExpr GhcPs))
transNLPatternEq m@(Match _ _ ps grhss) = do
  (ps', s) <- runStateT (mapM transNLPatterns ps) (0, [])
  grhss' <- addNLToGRHSs s grhss
  return (m { m_pats = ps', m_grhss = grhss' })

addNLToGRHSs :: (Integer, [RdrName]) -> GRHSs GhcPs (LHsExpr GhcPs) -> Hsc (GRHSs GhcPs (LHsExpr GhcPs))
addNLToGRHSs s (GRHSs x eqs bs) = do
  eqs' <- mapM (\(L l e) -> L l <$> addNLGuard s e) eqs
  bs' <- addNLLocalDefs s bs
  return (GRHSs x eqs' bs')

addNLGuard :: (Integer, [RdrName]) -> GRHS GhcPs (LHsExpr GhcPs) -> Hsc (GRHS GhcPs (LHsExpr GhcPs))
addNLGuard (i,vs) (GRHS x gs e) = do
  p <- liftQ (genNLFunPat (map (mkName . occNameString . occName) vs))
  p' <- case convertToPat Generated noSrcSpan p of
      Right x -> return x
      Left _  -> error $ "How did this happen?: " ++ show p
  let numericArgs = map (mkName . ("arg" ++) . show)[0..i-1]
  ge <- liftQ (return $ mkNestedTupleE numericArgs)
  ge' <- case convertToHsExpr Generated noSrcSpan ge of
      Right x -> return x
      Left _  -> error $ "How did this happen?: " ++ show ge
  let g = noLoc (BindStmt noExtField p' ge' noSyntaxExpr noSyntaxExpr)
  return (GRHS x (gs ++ [g]) e)
  where
    mkNestedTupleE [] = ConE '()
    mkNestedTupleE [v] = VarE v
    mkNestedTupleE (v:vs') = mkTupleE [VarE v, mkNestedTupleE vs']

genNLFunPat :: [TH.Name] -> PatQ
genNLFunPat vs = do
    let uniqueVs = nubOrd vs
        tP = mkTupleP $ map VarP uniqueVs
    vE <- [| (\a -> [b | b@($(return tP)) <- $(return $ VarE (mkName "nlHelperInv")) a]) |]
    ViewP vE <$> [p| $(return tP):_ |]


addNLLocalDefs :: (Integer, [RdrName]) -> LHsLocalBinds GhcPs -> Hsc (LHsLocalBinds GhcPs)
addNLLocalDefs s (L l b) = L l <$> case b of
  HsValBinds _ (ValBinds _ bs sigs) -> mkHsValBindsWith bs sigs
  HsIPBinds xhib hib -> undefined
  EmptyLocalBinds _ -> mkHsValBindsWith emptyBag []
  _ -> error "shut up"
  where
    mkHsValBindsWith bs sigs = do
      (liftedDefs, liftedSigs) <- mkLiftedDef s
      (inverseDefs, inverseSigs) <- mkInverseFun s
      return (HsValBinds noExtField (ValBinds noExtField (listToBag (map noLoc (liftedDefs ++ inverseDefs)) `unionBags` bs) (sigs ++ map noLoc (liftedSigs ++ inverseSigs))))


mkWithTH :: ([TH.Name] -> DecsQ) -> (Integer, [RdrName]) -> Hsc ([HsBind GhcPs], [Sig GhcPs])
mkWithTH f (_, vs) =  do
  ds <- liftQ (f (map (mkName . occNameString . occName) vs))
  let extractFun (L _ (ValD _ x)) = Just (Left  x)
      extractFun (L _ (SigD _ x)) = Just (Right x)
      extractFun _                 = Nothing
  partitionEithers . mapMaybe extractFun <$>
    case convertToHsDecls Generated noSrcSpan ds of
      Right x -> return x
      Left _  -> error $ "How did this happen?: " ++ show ds

mkInverseFun :: (Integer, [RdrName]) -> Hsc ([HsBind GhcPs], [Sig GhcPs])
mkInverseFun = mkWithTH genNLInverseFun

mkLiftedDef :: (Integer, [RdrName]) -> Hsc ([HsBind GhcPs], [Sig GhcPs])
mkLiftedDef = mkWithTH genNLLiftedFun

genNLLiftedFun :: [TH.Name] -> DecsQ
genNLLiftedFun vs = do
  let uniqueVs = nubOrd vs
      liftedName = mkName "nlHelperFL" --TODO: Check naming, outsource?
      vsTupleExpr = mkLiftedNestedTupleE vs
      body = NormalB $ foldl (\expr' v -> AppE (VarE 'returnFLF) (LamE [VarP v] expr')) vsTupleExpr (reverse uniqueVs)
      liftedTy = AppT (ConT ''FL) $
        foldr (mkLiftedArrowT . VarT) (mkLiftedNestedTupleT vs) uniqueVs
  return [TH.FunD liftedName [Clause [] body []], TH.SigD liftedName liftedTy]
 where
  mkLiftedArrowT ty1 ty2 = applyType (ConT ''(-->)) [ty1, ty2]
  mkLiftedNestedTupleE [] = AppE (VarE 'returnFL) $ ConE '()
  mkLiftedNestedTupleE [v] = VarE v
  mkLiftedNestedTupleE (v:vs') = AppE (VarE 'returnFL) $ applyExp (ConE 'Tuple2FL) [VarE v, mkLiftedNestedTupleE vs']
  mkLiftedNestedTupleT [] = ConT '()
  mkLiftedNestedTupleT [v] = VarT v
  mkLiftedNestedTupleT (v:vs') = applyType (ConT ''Tuple2FL) [VarT v, mkLiftedNestedTupleT vs']

genNLInverseFun :: [TH.Name] -> DecsQ
genNLInverseFun vs = do
    let uniqueVs = nubOrd vs
        nlHelperTy = ForallT (map PlainTV uniqueVs) [] $
            foldr (mkArrowT . VarT) (mkNestedTupleT vs) uniqueVs
        liftedName = mkName "nlHelperFL"
    genInverse "nlHelper" nlHelperTy [] False liftedName
  where
    mkNestedTupleT [] = ConT '()
    mkNestedTupleT [v] = VarT v
    mkNestedTupleT (v:vs') = mkTupleT [VarT v, mkNestedTupleT vs']
{-genNLInverseFun originalArity = do
  let liftedName = mkName "nlHelperFL"
      invName = mkName "nlHelperInv" --TODO: Check naming, outsource?
      ids = take originalArity [-1, -2 ..]
      argExps = map (mkFreeP . mkIntExp) ids
  funPatExp <- genLiftedApply (VarE liftedName) argExps
  hName <- newName "h"
  hsName <- newName "hs"
  resName <- newName "res"
  let invArgPats = [VarP resName]
      lambda = LamE [VarP hName] $ mkTupleE $ map (\i -> applyExp (VarE 'retrieve) [mkIntExp i, VarE hName]) ids
      body = NormalB $ applyExp (VarE 'fmap) [lambda, VarE hsName]
      expr = applyExp (VarE 'matchFL) [VarE resName, funPatExp]
      localDec = TH.ValD (VarP hsName) (NormalB $ AppE (VarE 'execFL) expr) []
  return $ TH.FunD invName [Clause invArgPats body [localDec]]-}

transNLPatterns :: LPat GhcPs -> NLTransM (LPat GhcPs)
transNLPatterns (L l p) = L l <$> case p of
  w@(WildPat _) -> return w
  VarPat x (L l' v) -> do
      (i, xs) <- get
      let v' = Unqual (mkVarOcc ("arg" ++ show i)) -- TODO might generate name shadowing
      put (i+1, xs ++ [v])
      return (VarPat x (L l' v'))
  AsPat x (L l' v) p' -> do
      (i, xs) <- get
      let v' = Unqual (mkVarOcc ("arg" ++ show i)) -- TODO might generate name shadowing
      put (i+1, xs ++ [v])
      p'' <- transNLPatterns p'
      return (AsPat x (L l' v') p'') --TODO: share code with above
  ListPat x ps -> ListPat x <$> mapM transNLPatterns ps
  LazyPat xlp xr -> undefined
  ParPat x p' -> ParPat x <$> transNLPatterns p'
  BangPat xbp xr -> undefined
  TuplePat xtp xrs box -> undefined
  SumPat xsp xr n i -> undefined
  ConPatIn gl hcd -> undefined
  ConPatOut gl tys vars vars' teb hcd hw -> undefined
  ViewPat xvp gl xr -> undefined
  SplicePat xsp (HsUntypedSplice _ d v e) -> panicAnyUnsafe "Splice" (d, v, e)
  LitPat xlp hl -> undefined
  NPat xp gl m_se se -> undefined
  NPlusKPat xpkp gl gl' hol se se' -> undefined
  SigPat xsp xr hwcb -> undefined
  CoPat xcp hw pat ty -> undefined
  XPat xp -> undefined
