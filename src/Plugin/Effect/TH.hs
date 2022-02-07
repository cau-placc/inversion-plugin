{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
module Plugin.Effect.TH where

import Control.Applicative
import Control.Monad

import Data.Bifunctor
import Data.List (intercalate, partition, sortOn, subsequences)
import Data.Tuple.Solo

import FastString

import Generics.SYB

import Language.Haskell.TH hiding (match)
import Language.Haskell.TH.Syntax (Name(..), NameFlavour(..), pkgString, mkNameG_v, OccName (OccName))

import Lexeme

import Plugin.Lifted
import Plugin.Effect.Monad
import Plugin.Effect.Tree
import Plugin.Trans.TysWiredIn


genInverses :: Name -> Type -> String -> DecsQ
genInverses liftedName originalTy originalString = do
  concat <$> sequence [genInverse originalString originalTy fixedArgs nonGround liftedName | fixedArgs <- fixedArgss, nonGround <- [False ..]]
  where
    (_ ,_ , originalTy') = decomposeForallT originalTy
    arity = arrowArity originalTy'
    fixedArgss = subsequences [0.. arity - 1]

mkInverseName :: String -> [Int] -> Bool -> Name
mkInverseName originalName fixedArgs nonGround
  | isLexVarSym (mkFastString originalName) = mkName $ originalName ++ "$$$" ++ concat ["-%" | nonGround] ++ intercalate "$" (map ((`replicate` '+') . succ) fixedArgs)
  | otherwise                               = mkName $ originalName ++ "Inv" ++ concat ["NG" | nonGround] ++ intercalate "_" (map show fixedArgs)

genInverse :: String -> Type -> [Int] -> Bool -> Name -> DecsQ
genInverse originalString originalTy fixedArgs nonGround liftedName = do
  let invName = mkInverseName originalString fixedArgs nonGround
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
            freeExps = zip nonFixedArgs $ map (mkFreeP . mkIntExp) ids
        fixedArgNames <- replicateM (length fixedArgs) (newName "arg")
        let toFLExps = zip fixedArgs $ map (AppE (VarE 'toFL) . VarE) fixedArgNames
            argExps = map snd $ sortOn fst $ freeExps ++ toFLExps
        funPatExp <- genLiftedApply (SigE (VarE liftedName) (AppT (ConT ''FL) (mkLifted (ConT ''FL) originalTy'))) argExps
        resName <- newName "res"
        let invArgPats = map VarP $ fixedArgNames ++ [resName]
            matchExp = applyExp (VarE 'matchFL) [VarE resName, funPatExp]
            returnExp = mkLiftedTupleE (map snd freeExps)
#ifdef PARALLEL
            searchFunNm = 'ps
#else
            searchFunNm = 'bfs
#endif
            bodyExp = applyExp (VarE 'map) [VarE (if nonGround then 'fromEither else 'fromIdentity), AppE (VarE searchFunNm) (applyExp (VarE 'evalWith)
              [ VarE (if nonGround then 'normalFormFL else 'groundNormalFormFL)
              , applyExp (VarE '(>>)) [matchExp, returnExp]])]
            body = NormalB bodyExp
        return $ FunD invName [Clause invArgPats body []]

  sequence [genPartialInverseSig, genPartialInverseFun]

--TODO: lift to q and throw error when length of list is > maxTupleArity
mkLiftedTupleE :: [Exp] -> Exp
mkLiftedTupleE []  = AppE (VarE 'return) (AppE (VarE 'to) (ConE '()))
mkLiftedTupleE xs  = AppE (VarE 'return) (applyExp liftedTupleConE xs)
  where
    -- TODO does this really work?
    liftedTupleConE = ConE $ mkNameG_v pkgName builtInModule tupleConName
    tupleConName | length xs == 1 = "SoloFL"
                 | otherwise      = "Tuple" ++ show (length xs) ++ "FL"
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
mkFreeP = AppE (VarE 'free)

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
mkTupleE [e] = AppE (ConE 'Solo) e
mkTupleE es  = TupE $ map Just es

mkTupleT :: [Type] -> Type
mkTupleT [ty] = AppT (ConT ''Solo) ty
mkTupleT tys  = applyType (TupleT (length tys)) tys

mkTupleP :: [Pat] -> Pat
mkTupleP [p] = ConP 'Solo [p]
mkTupleP ps' = TupP ps'

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
  return $ DataD [] name (KindedTV mVar (AppT (AppT ArrowT StarT) StarT) : map PlainTV tyVarNames) Nothing [con] []

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

renameTcInfo :: String -> TcInfo -> TcInfo
renameTcInfo suffix (TcInfo tcNm vs cis) = TcInfo tcNm (map rename vs) (map renameConInfo cis)
  where renameConInfo (ConInfo conNm tys) = ConInfo conNm (map renameType tys)
        renameType = everywhere (mkT renameVar)
        renameVar (VarT varNm) = VarT (rename varNm)
        renameVar ty = ty
        rename (Name (OccName str) nf) = Name (OccName (str ++ suffix)) nf

mkNarrowEntry :: Name -> ConInfo -> Exp
mkNarrowEntry idName conInfo = mkTupleE [conExp, mkIntExp (conArity conInfo)]
  where conExp = foldl (\conExp' idOffset -> AppE conExp' (mkFreeP (mkPlus (VarE idName) (mkIntExp idOffset)))) (ConE $ conName conInfo) [0 .. conArity conInfo - 1]

mkPlus :: Exp -> Exp -> Exp
mkPlus e1 e2 = applyExp (VarE '(+)) [e1, e2]

genMTy :: Q Type
genMTy = VarT <$> newName "m"

genLifted :: Type -> Type -> [Type] -> Type -> DecsQ
genLifted originalTc liftedTc liftedTyVars mTy = do
  let genLiftedApp n =
        let relevantVars = take n liftedTyVars
        in TySynInstD $ TySynEqn Nothing (mkLifted mTy (applyType originalTc relevantVars)) (applyType liftedTc (map (mkLifted mTy) relevantVars))
  return $ map genLiftedApp [0 .. length liftedTyVars]

genInstances :: Dec -> Dec -> DecsQ
genInstances (ClassD _ originalName _ _ _) (ClassD _ liftedName liftedTyVarBndrs _ _) =
  let liftedTyVarNames = map getTyVarBndrName liftedTyVarBndrs
      liftedTyVars = map VarT liftedTyVarNames
      originalTc = ConT originalName
      liftedTc = ConT liftedName
  in genLifted originalTc liftedTc liftedTyVars (ConT ''FL)
genInstances (TySynD _ _ _) (TySynD _ _ _) = do
  return []
genInstances originalDataDec liftedDataDec = do

  let originalTcInfo = renameTcInfo "a" $ extractTcInfo id originalDataDec
      originalTc = ConT $ tcName originalTcInfo
      originalTyVarNames = tcVarNames originalTcInfo
      originalTyVars = map VarT originalTyVarNames
      originalTy = applyType (ConT $ tcName originalTcInfo) originalTyVars
      originalConInfos = tcConInfos originalTcInfo
      originalConArgs = concatMap conArgs originalConInfos
  let liftedTcInfo = renameTcInfo "b" $ extractTcInfo innerType liftedDataDec
      liftedTc = AppT (ConT $ tcName liftedTcInfo) mTy
      (mvar, liftedTyVarNames) = case tcVarNames liftedTcInfo of { x:xs -> (x,xs); _ -> error "TH: unexpected unlifted constructor"} -- Discard the monad parameter here
      liftedTyVars = map VarT liftedTyVarNames
      liftedTy = applyType (ConT $ tcName liftedTcInfo) $ ConT ''FL : liftedTyVars
      liftedConInfos = tcConInfos liftedTcInfo
      liftedConArgs = map (replaceMTyVar mvar (ConT ''FL)) $ concatMap conArgs liftedConInfos
      mTy = VarT mvar

  let genHasPrimitiveInfo = do
        let body = NormalB $ ConE 'NoPrimitive
            dec = FunD 'primitiveInfo [Clause [] body []]
            ctxt = map mkHasPrimitiveInfoConstraint liftedConArgs
        return $ InstanceD Nothing ctxt (mkHasPrimitiveInfoConstraint liftedTy) [dec]

      genNarrowable = do
        jName <- newName "j"
        let entries = map (mkNarrowEntry jName) liftedConInfos
            body = NormalB $ ListE entries
            dec = FunD 'narrow [Clause [VarP jName] body []]
            ctxt = map mkHasPrimitiveInfoConstraint liftedConArgs
        return $ InstanceD Nothing ctxt (mkNarrowableConstraint liftedTy) [dec]

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
              let failClause = Clause [WildP, WildP] (NormalB $ VarE 'Control.Applicative.empty) []
              return $ FunD 'match (clauses ++ [failClause])
        dec <- genMatch
        let ctxt = map mkConvertibleConstraint originalConArgs ++
                     map mkMatchableConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkMatchableConstraint originalTy) [dec]

      genNormalForm = do
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
            ctxt = zipWith mkNormalFormConstraint originalConArgs liftedConArgs
        return $ InstanceD Nothing ctxt (mkNormalFormConstraint originalTy liftedTy) [dec]

      genInvertible = do
        let ctxt = map mkInvertibleConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkInvertibleConstraint originalTy) [] :: Q Dec

  (++) <$> genLifted originalTc liftedTc liftedTyVars mTy
       <*> sequence [genHasPrimitiveInfo, genNarrowable, genConvertible, genMatchable, genNormalForm, genInvertible]

replaceMTyVar :: Name -> Type -> Type -> Type
replaceMTyVar var replacement = go
  where
    go :: Type -> Type
    go ty = case ty of
      AppT ty1 ty2       -> AppT (go ty1) (go ty2)
      VarT n | n == var  -> replacement
             | otherwise -> VarT n
      _                  -> ty

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

mkNormalFormConstraint :: Type -> Type -> Type
mkNormalFormConstraint ty1 ty2 = applyType (ConT ''NormalForm) [ty1, ty2]

mkInvertibleConstraint :: Type -> Type
mkInvertibleConstraint ty = applyType (ConT ''Invertible) [ty]
