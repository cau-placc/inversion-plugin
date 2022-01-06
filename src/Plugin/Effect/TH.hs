{-# LANGUAGE TemplateHaskell #-}
module Plugin.Effect.TH where

import Control.Applicative
import Control.Monad

import Data.Bifunctor
import Data.List ( intercalate, partition, sortOn, subsequences )

import FastString

import Language.Haskell.TH hiding (match)
import Language.Haskell.TH.Syntax (Name(..), NameFlavour(..), pkgString, mkNameG_v)

import Lexeme

import Plugin.Effect.Monad
import Plugin.Effect.Tree
import Plugin.Trans.TysWiredIn


genInverses :: Name -> Type -> String -> DecsQ
genInverses liftedName originalTy originalString = do
  concat <$> sequence [genInverse originalString originalTy fixedArgs useGNF liftedName | fixedArgs <- fixedArgss, useGNF <- [False ..]]
  where
    (_ ,_ , originalTy') = decomposeForallT originalTy
    arity = arrowArity originalTy'
    fixedArgss = subsequences [0.. arity - 1]

mkInverseName :: String -> [Int] -> Bool -> Name
mkInverseName originalName fixedArgs useGNF
  | isLexVarSym (mkFastString originalName) = mkName $ originalName ++ "$$$" ++ concat ["-%" | useGNF] ++ intercalate "$" (map ((`replicate` '+') . succ) fixedArgs)
  | otherwise                               = mkName $ originalName ++ "Inv" ++ concat ["NF" | useGNF] ++ intercalate "_" (map show fixedArgs)

genInverse :: String -> Type -> [Int] -> Bool -> Name -> DecsQ
genInverse originalString originalTy fixedArgs useGNF liftedName = do
  let invName = mkInverseName originalString fixedArgs useGNF
      (originalTyVarBndrs, originalCxt, originalTy') = decomposeForallT originalTy
      (originalArgTys, originalResTy) = arrowUnapply originalTy'
      (fixedOriginalArgTys, nonFixedOriginalArgTys) = partitionByIndices fixedArgs originalArgTys

  let genPartialInverseSig = do
        let invArgTys = fixedOriginalArgTys ++ [originalResTy]
            invResTy = applyType ListT [mkTupleT nonFixedOriginalArgTys]
            invCxt = originalCxt ++ map (mkLifted (ConT ''FL)) originalCxt ++
              map mkInvertibleConstraint  (originalResTy : nonFixedOriginalArgTys) ++
              map mkConvertibleConstraint fixedOriginalArgTys
            invTy = ForallT originalTyVarBndrs invCxt $ foldr mkArrowT invResTy invArgTys
        return $ SigD invName invTy

      genPartialInverseFun = do
        let originalArity = arrowArity originalTy'
            nonFixedArgs = filter (`notElem` fixedArgs) [0 .. originalArity - 1]
            ids = take (originalArity - length fixedArgs) [-1, -2 ..]
            freePExps = zip nonFixedArgs $ map (mkFreeP . mkIntExp) ids --TODO freeP = freeFL
        fixedArgNames <- replicateM (length fixedArgs) (newName "arg")
        let toPExps = zip fixedArgs $ map (AppE (VarE 'toFL) . VarE) fixedArgNames
            argExps = map snd $ sortOn fst $ freePExps ++ toPExps
        funPatExp <- genLiftedApply (SigE (VarE liftedName) (AppT (ConT ''FL) (mkLifted (ConT ''FL) originalTy'))) argExps
        resName <- newName "res"
        let invArgPats = map VarP $ fixedArgNames ++ [resName]
            matchExp = applyExp (VarE 'matchFL) [VarE resName, funPatExp]
            returnExp = mkLiftedTupleE (map snd freePExps)
        -- evalExp <- [| \m r -> map from $ bfs $ evalFL (m >> r) |]
        let bodyExp = applyExp (VarE 'map) [VarE (if useGNF then 'fromIdentity else 'fromEither), AppE (VarE 'bfs) (applyExp (VarE 'evalWith)
              [ VarE (if useGNF then 'groundNormalFormFL else 'normalFormFL)
              , applyExp (VarE '(>>)) [matchExp, returnExp]])]
            body = NormalB bodyExp
        return $ FunD invName [Clause invArgPats body []]

  sequence [genPartialInverseSig, genPartialInverseFun]

--TODO: lift to q and throw error when length of list is > maxTupleArity
mkLiftedTupleE :: [Exp] -> Exp
mkLiftedTupleE [] = AppE (VarE 'return) (AppE (VarE 'to) (ConE '()))
mkLiftedTupleE [x] = x
mkLiftedTupleE xs = AppE (VarE 'return) (applyExp liftedTupleConE xs)
  where
    -- TODO does this really work?
    liftedTupleConE = ConE $ mkNameG_v pkgName builtInModule ("Tuple" ++ show (length xs) ++ "FL")
    pkgName = case 'mkLiftedTupleE of
      Name _ (NameG _ p _) -> pkgString p
      _                    -> "inversion-plugin"

partitionByIndices :: [Int] -> [a] -> ([a], [a])
partitionByIndices is = bimap (map snd) (map snd) . partition ((`elem` is) . fst) . zip [0 ..]

decomposeForallT :: Type -> ([TyVarBndr], [Type], Type)
decomposeForallT (ForallT bndrs ctxt ty) = (bndrs, ctxt, ty)
decomposeForallT ty                      = ([], [], ty)

getTyVarBndrName :: TyVarBndr -> Name
getTyVarBndrName (PlainTV  name  ) = name
getTyVarBndrName (KindedTV name _) = name

mkFreeP :: Exp -> Exp
mkFreeP = AppE (VarE 'freeFL)

mkIntExp :: Int -> Exp
mkIntExp = LitE . IntegerL . fromIntegral

applyExp :: Exp -> [Exp] -> Exp
applyExp = foldl AppE

applyExp' :: ExpQ -> [ExpQ] -> ExpQ
applyExp' = foldl appE

unapplyExp :: Exp -> (Exp, [Exp])
unapplyExp (AppE e1 e2) = let (e, es) = unapplyExp e1 in (e, es ++ [e2])
unapplyExp e            = (e, [])

genLiftedApply :: Exp -> [Exp] -> ExpQ
genLiftedApply = foldM (\f arg -> newName "v" >>= \vName -> return $ applyExp (VarE '(>>=)) [f, LamE [ConP 'Func [VarP vName]] $ AppE (VarE vName) arg])

mkTupleE :: [Exp] -> Exp
mkTupleE [e] = e
mkTupleE es  = TupE $ map Just es

mkTupleT :: [Type] -> Type
mkTupleT [ty] = ty
mkTupleT tys  = applyType (TupleT (length tys)) tys

mkTupleP :: [Pat] -> Pat
mkTupleP [p] = p
mkTupleP ps  = TupP ps

mkArrowT :: Type -> Type -> Type
mkArrowT ty1 ty2 = applyType ArrowT [ty1, ty2]

applyType :: Type -> [Type] -> Type
applyType = foldl AppT

arrowUnapply :: Type -> ([Type], Type)
arrowUnapply (AppT (AppT ArrowT ty1) ty2) = (ty1 : tys, ty)
  where (tys, ty) = arrowUnapply ty2
arrowUnapply ty                           = ([], ty)

arrowArity :: Type -> Int
arrowArity = length . fst . arrowUnapply

--------------------------------------------------------------------------------

genLiftedTupleDataDecl :: Int -> DecQ
genLiftedTupleDataDecl ar = do
  let name = mkName $ "Tuple" ++ show ar ++ "FL"
  mVar <- newName "m"
  tyVarNames <- replicateM ar (newName "a")
  let con = NormalC name $ map (\tyVarName -> (Bang NoSourceUnpackedness NoSourceStrictness, AppT (VarT mVar) (VarT tyVarName))) tyVarNames
  return $ DataD [] name (map PlainTV (mVar : tyVarNames)) Nothing [con] []

genLiftedTupleDataDeclAndInstances :: Int -> DecsQ
genLiftedTupleDataDeclAndInstances ar = do
  TyConI originalDataDecl <- reify $ tupleTypeName ar
  liftedDataDecl <- genLiftedTupleDataDecl ar
  instances <- genInstances originalDataDecl liftedDataDecl
  return $ liftedDataDecl : instances

--------------------------------------------------------------------------------

data ConInfo = ConInfo { conName :: Name, conArgs :: [Type] }

conArity :: ConInfo -> Int
conArity = length . conArgs

extractConInfo :: (Type -> Type) -> Con -> ConInfo
extractConInfo f (NormalC n btys) = ConInfo n (map (f . snd) btys)
extractConInfo _ _ = error "mkConInfo: unsupported"
--TODO: missing constructors

data TcInfo = TcInfo { tcName :: Name, tcVarNames :: [Name], tcConInfos :: [ConInfo] }

tcArity :: TcInfo -> Int
tcArity = length . tcVarNames

extractTcInfo :: (Type -> Type) -> Dec -> TcInfo
extractTcInfo f (DataD _ tcNm tyVars _ cons _) = TcInfo tcNm (map getTyVarBndrName tyVars) (map (extractConInfo f) cons)
extractTcInfo f (NewtypeD _ tcNm tyVars _ con _) = TcInfo tcNm (map getTyVarBndrName tyVars) [extractConInfo f con]
extractTcInfo _ _ = error "extractTcInfo: unsupported"

mkNarrowEntry :: Name -> ConInfo -> Exp
mkNarrowEntry idName conInfo = mkTupleE [conExp, AppE (ConE 'Left) (mkIntExp (conArity conInfo))]
  where conExp = foldl (\conExp' idOffset -> AppE conExp' (mkFreeP (mkPlus (VarE idName) (mkIntExp idOffset)))) (ConE $ conName conInfo) [0 .. conArity conInfo - 1]

mkPlus :: Exp -> Exp -> Exp
mkPlus e1 e2 = applyExp (VarE '(+)) [e1, e2]

genMTy :: Q Type
genMTy = VarT <$> newName "m"

genInstances :: Dec -> Dec -> DecsQ
genInstances (ClassD _ originalName _ _ _) (ClassD _ liftedName liftedTyVarBndrs _ _) = do
  let liftedTyVarNames = map getTyVarBndrName liftedTyVarBndrs
      liftedTyVars = map VarT liftedTyVarNames
      originalTc = ConT originalName
      liftedTc = ConT liftedName
      mTy = ConT ''FL
  let genOne n =
        let relevantVars = take n liftedTyVars
        in TySynInstD $ TySynEqn Nothing (mkLifted mTy (applyType originalTc relevantVars)) (applyType liftedTc (map (mkLifted mTy) relevantVars))
  return $ map genOne [0 .. length liftedTyVars] :: DecsQ
genInstances (TySynD originalName _ _) (TySynD liftedName liftedTyVarBndrs _) = do
  let liftedTyVarNames = map getTyVarBndrName liftedTyVarBndrs
      liftedTyVars = map VarT liftedTyVarNames
      originalTc = ConT originalName
  mTy <- genMTy
  let liftedTc = AppT (ConT liftedName) mTy
  let genOne n =
        let relevantVars = take n liftedTyVars
        in TySynInstD $ TySynEqn Nothing (mkLifted mTy (applyType originalTc relevantVars)) (applyType liftedTc (map (mkLifted mTy) relevantVars))
  return $ map genOne [0 .. length liftedTyVars] :: DecsQ
genInstances originalDataDec liftedDataDec = do
  mTy <- genMTy

  let originalTcInfo = extractTcInfo id originalDataDec
      originalTc = ConT $ tcName originalTcInfo
      originalTyVarNames = tcVarNames originalTcInfo
      originalTyVars = map VarT originalTyVarNames
      originalTy = applyType (ConT $ tcName originalTcInfo) originalTyVars
      originalConInfos = tcConInfos originalTcInfo
      originalConArgs = concatMap conArgs originalConInfos
  let liftedTcInfo = extractTcInfo innerType liftedDataDec
      liftedTc = AppT (ConT $ tcName liftedTcInfo) mTy
      liftedTyVarNames = tail $ tcVarNames liftedTcInfo -- Discard the monad parameter here
      liftedTyVars = map VarT liftedTyVarNames
      liftedTy = applyType (ConT $ tcName liftedTcInfo) $ ConT ''FL : liftedTyVars
      liftedConInfos = tcConInfos liftedTcInfo
      liftedConArgs = concatMap conArgs liftedConInfos

  let genHasPrimitiveInfo = return $ InstanceD Nothing [] (mkHasPrimitiveInfoConstraint liftedTy) [] :: Q Dec

      genNarrowable = do
        jName <- newName "j"
        let entries = map (mkNarrowEntry jName) liftedConInfos
            body = NormalB $ ListE entries
            dec = FunD 'narrow [Clause [WildP, VarP jName, WildP] body []]
            ctxt = map mkNarrowableConstraint liftedConArgs ++ map mkHasPrimitiveInfoConstraint liftedConArgs
        return $ InstanceD Nothing ctxt (mkNarrowableConstraint liftedTy) [dec]

      genLifted = do
        let genOne n =
              let relevantVars = take n liftedTyVars
              in TySynInstD $ TySynEqn Nothing (mkLifted mTy (applyType originalTc relevantVars)) (applyType liftedTc (map (mkLifted mTy) relevantVars))
        return $ map genOne [0 .. length liftedTyVars] :: DecsQ

      genConvertible = do
        let genTo = do
              let genMatch originalConInfo liftedConInfo = do
                    argNames <- replicateM (conArity originalConInfo) (newName "x")
                    let pat = ConP (conName originalConInfo) $ map VarP argNames
                        body = NormalB $ applyExp (ConE $ conName liftedConInfo) $ map (AppE (VarE 'toFL) . VarE) argNames
                    return $ Match pat body []
              matches <- zipWithM genMatch originalConInfos liftedConInfos
              arg <- newName "arg"
              return $ FunD 'to [Clause [VarP arg] (NormalB (CaseE (VarE arg) matches)) []]
            genFrom = do
              ff <- newName "ff"
              let genMatch liftedConInfo originalConInfo = do
                    argNames <- replicateM (conArity liftedConInfo) (newName "x")
                    let pat = ConP (conName liftedConInfo) $ map VarP argNames
                        body = NormalB $ applyExp (ConE $ conName originalConInfo) $ map (AppE (VarE ff) . VarE) argNames
                    return $ Match pat body []
              arg <- newName "arg"
              matches <- zipWithM genMatch liftedConInfos originalConInfos
              return $ FunD 'fromWith [Clause [VarP ff, VarP arg] (NormalB (CaseE (VarE arg) matches)) []]
        let ctxt = map mkConvertibleConstraint originalConArgs
        InstanceD Nothing ctxt (mkConvertibleConstraint originalTy) <$>
          sequence [genTo, genFrom]

      genMatchable = do
        let genMatch = do
              let genClause originalConInfo liftedConInfo = do
                    originalArgNames <- replicateM (conArity originalConInfo) (newName "x")
                    liftedArgNames <- replicateM (conArity liftedConInfo) (newName "y")
                    let originalPat = ConP (conName originalConInfo) $ map VarP originalArgNames
                        liftedPat = ConP (conName liftedConInfo) $ map VarP liftedArgNames
                        body = NormalB $ foldr (\e1 e2 -> applyExp (VarE '(>>)) [e1, e2]) (AppE (VarE 'return) (ConE '())) $ zipWith (\originalArgName liftedArgName -> applyExp (VarE 'matchFL) [VarE originalArgName, VarE liftedArgName]) originalArgNames liftedArgNames
                    return $ Clause [originalPat, liftedPat] body []
              clauses <- zipWithM genClause originalConInfos liftedConInfos
              let failClause = Clause [WildP, WildP] (NormalB $ VarE 'empty) []
              return $ FunD 'match (clauses ++ [failClause])
        dec <- genMatch
        let ctxt = map mkConvertibleConstraint originalConArgs ++
                     map mkMatchableConstraint originalConArgs ++
                     map (mkHasPrimitiveInfoConstraint . mkLifted (ConT ''FL)) originalConArgs
        return $ InstanceD Nothing ctxt (mkMatchableConstraint originalTy) [dec]

      genGroundable = do
        nfName <- newName "nf"
        let genMatch liftedConInfo = do
              let liftedConName = conName liftedConInfo
                  liftedConArity = conArity liftedConInfo
              liftedArgNames <- replicateM liftedConArity (newName "x")
              freshLiftedArgNames <- replicateM liftedConArity (newName "y")
              let pat = ConP liftedConName $ map VarP liftedArgNames
                  body = NormalB $ foldr (\ (liftedArgName, freshLiftedArgName) e -> applyExp (VarE '(>>=)) [AppE (VarE nfName) (VarE liftedArgName), LamE [VarP freshLiftedArgName] e]) (AppE (VarE 'return) $ AppE (VarE 'pure) $ applyExp (ConE liftedConName) $ map VarE freshLiftedArgNames) $ zip liftedArgNames freshLiftedArgNames
              return $ Match pat body []
        matches <- mapM genMatch liftedConInfos
        let body = NormalB (LamCaseE matches)
            dec = FunD 'normalFormWith [Clause [VarP nfName] body []]
            ctxt = zipWith mkNFConstraint originalConArgs liftedConArgs
        return $ InstanceD Nothing ctxt (mkNFConstraint originalTy liftedTy) [dec]

      genInvertible = do
        let ctxt = [ mkConvertibleConstraint originalTy
                   , mkMatchableConstraint originalTy
                   , mkNFConstraint originalTy (mkLifted (ConT ''FL) originalTy)
                   ]
        return $ InstanceD Nothing ctxt (mkInvertibleConstraint originalTy) [] :: Q Dec

  (++) <$> genLifted <*> sequence [genHasPrimitiveInfo, genNarrowable, genConvertible, genMatchable, genGroundable, genInvertible]

innerType :: Type -> Type
innerType (AppT (VarT _) ty) = ty
innerType ty = error $ "Plugin.Effect.TH.innerType: incorrect usage on -> " ++ show ty

mkLifted :: Type -> Type -> Type
mkLifted mty ty = applyType (ConT ''Lifted) [mty, ty]

mkHasPrimitiveInfoConstraint :: Type -> Type
mkHasPrimitiveInfoConstraint ty = applyType (ConT ''HasPrimitiveInfo) [ty]

mkNarrowableConstraint :: Type -> Type
mkNarrowableConstraint ty = applyType (ConT ''Narrowable) [ty]

mkConvertibleConstraint :: Type -> Type
mkConvertibleConstraint ty = applyType (ConT ''Convertible) [ty]

mkMatchableConstraint :: Type -> Type
mkMatchableConstraint ty = applyType (ConT ''Matchable) [ty]

mkNFConstraint :: Type -> Type -> Type
mkNFConstraint ty1 ty2 = applyType (ConT ''NF) [ty1, ty2]

mkInvertibleConstraint :: Type -> Type
mkInvertibleConstraint ty = applyType (ConT ''Invertible) [ty]
