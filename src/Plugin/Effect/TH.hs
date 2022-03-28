{-# LANGUAGE CPP               #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE FlexibleInstances #-}
module Plugin.Effect.TH where

import Control.Applicative
import Control.Monad

import Data.Bifunctor
import Data.List (intercalate, partition, sortOn, subsequences, nub)
import qualified Data.Map as Map
import Data.Maybe
import Data.Tuple.Solo

import FastString
import GHC (mkModule, mkModuleName)
import GhcPlugins (DefUnitId(DefUnitId), UnitId (DefiniteUnitId), InstalledUnitId (InstalledUnitId))
import Lexeme

import Generics.SYB

import Language.Haskell.TH hiding (match)
import Language.Haskell.TH.Syntax (Name(..), NameFlavour(..), pkgString, mkNameG_v, OccName (OccName), PkgName (PkgName), ModName (ModName), qRecover, showName', NameIs (Applied))


import Plugin.Lifted
import Plugin.Effect.Monad
import Plugin.Trans.TysWiredIn
import Plugin.Trans.Import (lookupSupportedBuiltInModule)

lookupBuiltin :: String -> Maybe String
lookupBuiltin "[]" = Just "NilFL"
lookupBuiltin ":"  = Just "ConsFL"
lookupBuiltin "()" = Just "UnitFL"
lookupBuiltin s | Just n <- tupleConArity s = Just $ "Tuple" ++ show n ++ "FL"
                | otherwise                 = Nothing
  where tupleConArity ('(':rest) = Just $ succ $ length $ takeWhile (== ',') rest
        tupleConArity _          = Nothing

liftTHName :: Name -> Name
liftTHName (Name (OccName str) flav) = Name withSuffix flav'
  where
    withSuffix | Just str' <- lookupBuiltin str = OccName str'
               | isLexVarSym (mkFastString str) = OccName $ str ++ "#"
               | isLexConSym (mkFastString str) = OccName $ str ++ "#"
               | otherwise                      = OccName $ str ++ "FL"
    flav' = case flav of
      NameS -> NameS
      NameQ mn -> NameQ mn
      NameU n -> NameU n
      NameL n -> NameL n
      NameG ns (PkgName pn) (ModName mn) ->
        let ghcModule = mkModule (DefiniteUnitId (DefUnitId (InstalledUnitId (mkFastString pn)))) (mkModuleName mn)
            (pkgNm', mdlNm') = maybe (pn, mn) (thisPkgName,) $
                               lookupSupportedBuiltInModule ghcModule
        in NameG ns (PkgName pkgNm') (ModName mdlNm')

liftTHNameQ :: Name -> Q Name
liftTHNameQ name = do
  let liftedName = liftTHName name
  reifiable <- qRecover (return False) (reify liftedName >> return True)
  if reifiable
    then return liftedName
    else fail $ "No inverse for " ++ show name

var :: Integer -> a
var _ = error "free is undefined outside of inverse contexts"

-- exp <- unType <$>  runQ (([|| (,) (var 1) (var 2) ||] :: Q (TExp (Bool, Bool))))
--putStrLn $(makeFreeMap (createIDMapping exp) >>= \fm -> convertExp fm exp >>= \e -> stringE $ pprint e)
--outClassInv :: InClass p => Name -> ExpQ -> p
--outClassInv _ = undefined

-- inv name = inClassInv [| var 1 |] [| var 2 |]
-- partialInv name x.. = inClassInv name [| x1 |] [| x2 |]

--inClassInv2 :: Name -> [ExpQ] -> ExpQ
--inClassInv2 = mkInClassInverse
--inClassInverse f []

getArity :: Name -> Q Int
getArity name = do
  info <- reify name
  (_, _, ty) <- decomposeForallT <$> case info of
    VarI _ ty' _     -> return ty'
    ClassOpI _ ty' _ -> return ty'
    _                -> fail $ show name ++ " is no function or class method."
  return $ arrowArity ty

partialInv :: Name -> [Int] -> ExpQ
partialInv name fixedArgIndices = do
  originalArity <- getArity name
  let validFixedArgIndices = [0 .. originalArity - 1]
      hint = "has to be a subsequence of " ++ show validFixedArgIndices
  when (any (`notElem` validFixedArgIndices) fixedArgIndices) $ fail $
    "Invalid argument index sequence for partial inverse provided (" ++ hint ++ ")."
  let nubbedFixedArgIndices = nub fixedArgIndices
      nonFixedArgIndices = filter (`notElem` fixedArgIndices) validFixedArgIndices
  fixedArgNames <- replicateM (length nubbedFixedArgIndices) (newName "fixedArg")
  let fixedArgExps = zip nubbedFixedArgIndices $ map VarE fixedArgNames
      nonFixedArgExps = zip nonFixedArgIndices $ map (AppE (VarE 'var) . mkIntExp) [0 ..]
      inClassExps = map snd $ sortOn fst $ fixedArgExps ++ nonFixedArgExps
  LamE (map VarP fixedArgNames) <$> inClassInv name (map return inClassExps)

{-inv2 :: Name -> ExpQ
inv2 name = do
  --TODO: folgendes auslagern, da häufig gebraucht
  info <- reify name
  (_, _, ty) <- decomposeForallT <$> case info of
    VarI _ ty' _     -> return ty'
    ClassOpI _ ty' _ -> return ty'
    _                -> fail $ show name ++ " is no function or class method."
  let originalArity = arrowArity ty

  inClassInv name (map (return . AppE (VarE 'var) . mkIntExp) [0 .. originalArity - 1])-}

--inv2 :: Name -> ExpQ
--inv2 name = partialInv2 name []

inOutClassInv :: Name -> [ExpQ] -> ExpQ -> ExpQ
inOutClassInv f = genInOutClassInverse f False

inClassInv :: Name -> [ExpQ] -> ExpQ
inClassInv f ins = [| \x -> $(inOutClassInv f ins [| x |]) |]

genInOutClassInverse :: Name -> Bool -> [ExpQ] -> ExpQ -> ExpQ
genInOutClassInverse name nonGround inClassExpQs outClassExpQ = do
  originalArity <- getArity name
  let numInClasses = length inClassExpQs
  when (originalArity /= numInClasses) $ fail $ "Wrong number of input classes provided (expected " ++ show originalArity ++ ", but got " ++ show numInClasses ++ ")"
  inClassExps <- sequence inClassExpQs
  outClassExp <- outClassExpQ
  -- We add the output class at the end of the input classes, so that the free variables of the output class appear at the end of the result tuples of inverses.
  let exps = inClassExps ++ [outClassExp]

  mapping <- makeFreeMap (createIDMapping exps)
  liftedName <- liftTHNameQ name
  resExp : argExps <- mapM (convertExp (map (second fst) mapping)) (outClassExp:inClassExps)
  funPatExp <- genLiftedApply (VarE liftedName) argExps
  let matchExp = applyExp (VarE 'lazyUnifyFL) [resExp, funPatExp]
      freeNames = map (fst . snd) mapping
      letExp = DoE [NoBindS matchExp, NoBindS returnExp ]
      returnExp = mkLiftedTupleE (map VarE freeNames)
      bodyExp = applyExp (VarE 'map) [VarE (if nonGround then 'fromEither else 'fromIdentity), applyExp (VarE 'evalFLWith)
        [ VarE (if nonGround then 'normalFormFL else 'groundNormalFormFL)
        , letExp]]
  bNm <- newName "b"
  let letDecs = [FunD bNm [Clause (map VarP freeNames) (NormalB bodyExp) []]]
  return $ LetE letDecs (applyExp (VarE bNm) (map (snd . snd) mapping))
  --TODO: explain why monomorph types, let generalisation does not take place, because the type of free1/2 leaks to the outside (as every free variable is part of the return value of an inverse)


-- $(partialInv 'map [| replicate 2 True |] [| free 1 |])
--TODO: inferenzsystem für erlaubte ausdrücke in input classes.
--TODO: TTH damit man falsche applications von free oder konstruktoren finden kann. pattern wären nicht ausreichend, da wir so keine freien variablen nicht-linear spezifizieren könnten, da syntaktisch verboten.
--TODO: mapping zu negativen zahlen

convertTExp :: [(Integer, Name)] -> TExp a -> Q Exp
convertTExp freeMap = convertExp freeMap . unType

convertExp :: [(Integer, Name)] -> Exp -> Q Exp
convertExp freeMap = \case
  VarE na -> return $ AppE (VarE 'toFL) (VarE na)
  ConE na ->
    reify na >>= \case
      DataConI _ ty _ -> createLambda na ty
      _ -> fail "unexpected result from reification of a constructor"
  LitE lit -> return $ AppE (VarE 'toFL) (LitE lit)
  AppE exp' exp2 -> case exp' of
    VarE na | na == 'Plugin.Effect.TH.var ->
                case exp2 of
                  _ | LitE (IntegerL i) <- exp2 -> case lookup i freeMap of
                                                      Nothing -> fail "internal error: free var not found"
                                                      Just n  -> return $ VarE n
                    | otherwise -> error "wrong form of input class" --TODO: improve error message. only integer literals are allowed. negative only with negativeliterals extensions.
            | otherwise   -> fail "forbidden function application in input/output specification of an inverse" --TODO
    _ -> AppE <$> convertExp freeMap exp' <*> convertExp freeMap exp2
  ParensE exp' -> ParensE <$> convertExp freeMap exp'
  InfixE m_exp exp' ma | isJust m_exp && isJust ma -> convertExp freeMap (applyExp exp' (map fromJust [m_exp, ma]))
  TupE m_exps | all isJust m_exps -> mkLiftedTupleE <$> mapM (convertExp freeMap . fromJust) m_exps
  ListE exps -> convertExp freeMap (foldr (\x xs -> applyExp (ConE '(:)) [x, xs]) (ConE '[]) exps)
  --TODO: handle wildcard/whole
  UnboundVarE na -> fail $ "Variable not in scope: " ++ show na
  e -> fail $ "unsupported syntax in convertExp: " ++ show e
  where
    createLambda name ty = do
      let (_, _, ty') = decomposeForallT ty
          argsNum = arrowArity ty'
      nms <- replicateM argsNum (newName "arg")
      return $ LamE (map VarP nms) (AppE (VarE 'return) (foldl AppE (ConE (liftTHName name)) (map VarE nms)))

makeFreeMap :: [(Integer, ID)] -> Q [(Integer, (Name, Exp))]
makeFreeMap = mapM (\(i1, i2) -> do
  nm <- newName $ "free" ++ show (abs i2)
  return (i1, (nm, AppE (VarE 'Plugin.Effect.Monad.free) (LitE (IntegerL i2)))))

createIDMapping :: [Exp] -> [(Integer, ID)]
createIDMapping exps = zip (nub $ map (\case
  AppE exp' exp2 -> case exp' of --TODO: integrate PM
    VarE na | na == 'var,
              LitE (IntegerL n) <- exp2 -> n
    _ -> error "cannot happen"
  _ -> error "cannot happen") $ listify (\case
  AppE exp' exp2 -> case exp' of
    VarE na | na == 'var,
              LitE (IntegerL _) <- exp2 -> True
            | otherwise   -> False
    _ -> False
  _ -> False) exps) [-1, -2 ..]

thisPkgName :: String
thisPkgName = case 'toFL of
  Name _ (NameG _ (PkgName s) _) -> s
  _                              -> error "could not deduce package name of the plugin package"

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
mkFreeP = AppE (VarE 'Plugin.Effect.Monad.free)

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

      genUnifiable = do
        let genUnify = do
              let genClause liftedConInfo = do
                    let liftedConArity = conArity liftedConInfo
                        liftedConName = conName liftedConInfo
                    liftedArgNames1 <- replicateM liftedConArity (newName "x")
                    liftedArgNames2 <- replicateM liftedConArity (newName "y")
                    let liftedPat1 = ConP liftedConName $ map VarP liftedArgNames1
                        liftedPat2 = ConP liftedConName $ map VarP liftedArgNames2
                        body = NormalB $ foldr (\e1 e2 -> applyExp (VarE '(>>)) [e1, e2]) (AppE (VarE 'return) (ConE '())) $ zipWith (\liftedArgName1 liftedArgName2 -> applyExp (VarE 'lazyUnifyFL) [VarE liftedArgName1, VarE liftedArgName2]) liftedArgNames1 liftedArgNames2
                    return $ Clause [liftedPat1, liftedPat2] body []
              clauses <- mapM genClause liftedConInfos
              let failClause = Clause [WildP, WildP] (NormalB $ VarE 'Control.Applicative.empty) []
              return $ FunD 'lazyUnify (clauses ++ [failClause])
        dec <- genUnify
        let ctxt = map mkUnifiableConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkUnifiableConstraint originalTy) [dec]

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
            ctxt = map mkNormalFormConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkNormalFormConstraint originalTy) [dec]

      genShowFree = do
        let genshowFree = do
              let genClause originalConInfo = do
                    let originalConArity = conArity originalConInfo
                    originalArgNames <- replicateM originalConArity (newName "x")
                    let originalPat = ConP (conName originalConInfo) $ map VarP originalArgNames
                    let conStrExp = LitE $ StringL $ showName' Applied $ conName originalConInfo
                    plusPlusExp <- [| (" " ++) |]
                    let argExps = map (AppE plusPlusExp . AppE (VarE 'showFree) . VarE) originalArgNames
                    let strListExp = foldr (\x xs -> applyExp (ConE '(:)) [x, xs]) (ConE '[]) (conStrExp:argExps)
                    wholeExp <- if originalConArity == 0 then return conStrExp else [| "(" ++ concat $(return strListExp) ++ ")" |]
                    let body = NormalB wholeExp
                    return $ Clause [originalPat] body []
              clauses <- mapM genClause originalConInfos
              return $ FunD 'showFree' clauses
        dec <- genshowFree
        let ctxt = map mkShowFreeConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkShowFreeConstraint originalTy) [dec]

      genInvertible = do
        let ctxt = [ mkConvertibleConstraint originalTy
                   , mkMatchableConstraint originalTy
                   , mkUnifiableConstraint originalTy
                   , mkNormalFormConstraint originalTy
                   , mkHasPrimitiveInfoConstraint (mkLifted (ConT ''FL) originalTy)
                   , mkShowFreeConstraint originalTy
                   ] ++ map mkInvertibleConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkInvertibleConstraint originalTy) [] :: Q Dec

  (++) <$> genLifted originalTc liftedTc liftedTyVars mTy
       <*> sequence [genHasPrimitiveInfo, genNarrowable, genConvertible, genMatchable, genUnifiable, genNormalForm, genShowFree, genInvertible]

replaceMTyVar :: Name -> Type -> Type -> Type
replaceMTyVar tvar replacement = go
  where
    go :: Type -> Type
    go ty = case ty of
      AppT ty1 ty2       -> AppT (go ty1) (go ty2)
      VarT n | n == tvar -> replacement
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

mkUnifiableConstraint :: Type -> Type
mkUnifiableConstraint ty = applyType (ConT ''Unifiable) [ty]

mkShowFreeConstraint :: Type -> Type
mkShowFreeConstraint ty = applyType (ConT ''ShowFree) [ty]

mkNormalFormConstraint :: Type -> Type
mkNormalFormConstraint ty = applyType (ConT ''NormalForm) [ty]

mkInvertibleConstraint :: Type -> Type
mkInvertibleConstraint ty = applyType (ConT ''Invertible) [ty]
