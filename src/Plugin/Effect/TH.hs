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
import Language.Haskell.TH.Syntax (Name(..), NameFlavour(..), pkgString, mkNameG_v, OccName (OccName), PkgName (PkgName), ModName (ModName))


import Plugin.Lifted
import Plugin.Effect.Monad
import Plugin.Effect.Tree
import Plugin.Trans.TysWiredIn
import Plugin.Trans.Import (lookupSupportedBuiltInModule)

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

lookupBuiltin :: String -> Maybe String
lookupBuiltin "[]" = Just "NilFL"
lookupBuiltin ":" = Just "ConsFL"
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

--runQ ([||  ||]) >>= print . (\(Name _ flav) -> flav) . (\(VarE s) -> s) . unType

-- TODO: rename to "var" or "unknown"
var :: Integer -> a
var _ = error "free is undefined outside of inverse contexts"

-- exp <- unType <$>  runQ (([|| (,) (var 1) (var 2) ||] :: Q (TExp (Bool, Bool))))
--putStrLn $(makeFreeMap (createIDMapping exp) >>= \fm -> convertExp fm exp >>= \e -> stringE $ pprint e)
--outClassInv :: InClass p => Name -> ExpQ -> p
--outClassInv _ = undefined

-- inv name = inClassInv [| var 1 |] [| var 2 |]
-- partialInv name x.. = inClassInv name [| x1 |] [| x2 |]

inClassInv2 :: Name -> [ExpQ] -> ExpQ
inClassInv2 = mkInClassInverse
--inClassInverse f []



inOutClassInv :: Name -> [ExpQ] -> ExpQ -> ExpQ
inOutClassInv = mkInOutClassInverse

--inClassInv2 :: Name -> [ExpQ] -> ExpQ
inClassInv :: Name -> [ExpQ] -> ExpQ
inClassInv f ins = [| \x -> $(inOutClassInv f ins [| x |]) |]

mkInOutClassInverse :: Name -> [ExpQ] -> ExpQ -> ExpQ
mkInOutClassInverse name expsQ outExpQ = do
  info <- reify name
  (_, _, ty) <- decomposeForallT <$> case info of
    VarI _ ty' _     -> return ty'
    ClassOpI _ ty' _ -> return ty'
    _                -> fail $ show name ++ " is no function or class method."
  let originalArity = arrowArity ty
  if originalArity == length expsQ
    then do
      exps <- sequence expsQ
      outExp <- outExpQ
      let allExps = exps ++ [outExp]
      mapping <- makeFreeMap (createIDMapping allExps)
      let liftedName = liftTHName name
      (outExp':argExps) <- mapM (convertExp (map (second fst) mapping)) (outExp:exps)
      funPatExp <- genLiftedApply (VarE liftedName) argExps
      let matchExp = applyExp (VarE 'lazyUnifyFL) [outExp', funPatExp]
          freeNames = map (fst . snd) mapping
          letExp = DoE [NoBindS matchExp, NoBindS returnExp ]
          returnExp = mkLiftedTupleE (map VarE freeNames)





          searchFunNm = 'bfs

          bodyExp = applyExp (VarE 'map) [VarE (if False {-nonGround-} then 'fromEither else 'fromIdentity), AppE (VarE searchFunNm) (applyExp (VarE 'evalWith)
            [ VarE (if False {-nonGround-} then 'normalFormFL else 'groundNormalFormFL)
            , letExp])]
      bNm <- newName "b"
      let letDecs = [FunD bNm [Clause (map VarP freeNames) (NormalB bodyExp) []]]
      return $ LetE letDecs (applyExp (VarE bNm) (map (snd . snd) mapping))
    else fail $ "Not enough arguments. Expected " ++ show originalArity ++ ", but received" ++ show (length expsQ) --TODO wrong number of arguments-}

instance InClass p => InClass (ExpQ -> p) where
  inClassInverse name args = \arg -> inClassInverse name (arg : args)

instance InClass ExpQ where
  inClassInverse name = mkInClassInverse name . reverse
class InClass p where
  inClassInverse :: Name -> [ExpQ] -> p

mkInClassInverse :: Name -> [ExpQ] -> ExpQ
mkInClassInverse name expsQ = do
  info <- reify name
  (_, _, ty) <- decomposeForallT <$> case info of
    VarI _ ty' _     -> return ty'
    ClassOpI _ ty' _ -> return ty'
    _                -> fail $ show name ++ " is no function or class method."
  let originalArity = arrowArity ty
  if originalArity == length expsQ
    then do
      exps <- sequence expsQ
      mapping <- makeFreeMap (createIDMapping exps)
      let liftedName = liftTHName name
      argExps <- mapM (convertExp (map (second fst) mapping)) exps
      funPatExp <- genLiftedApply (VarE liftedName) argExps
      resName <- newName "res"
      let invArgPats = [resName]
          matchExp = applyExp (VarE 'matchFL) [VarE resName, funPatExp]
          freeNames = map (fst . snd) mapping
          letExp = DoE [NoBindS matchExp, NoBindS returnExp ]
          returnExp = mkLiftedTupleE (map VarE freeNames)





          searchFunNm = 'bfs

          bodyExp = applyExp (VarE 'map) [VarE (if False {-nonGround-} then 'fromEither else 'fromIdentity), AppE (VarE searchFunNm) (applyExp (VarE 'evalWith)
            [ VarE (if False {-nonGround-} then 'normalFormFL else 'groundNormalFormFL)
            , letExp])]
      bNm <- newName "b"
      let letDecs = [FunD bNm [Clause (map VarP freeNames) (NormalB bodyExp) []]]
      return $ LamE (map VarP invArgPats) (LetE letDecs (applyExp (VarE bNm) (map (snd . snd) mapping)))
    else fail $ "Not enough arguments. Expected " ++ show originalArity ++ ", but received" ++ show (length expsQ)
{-mkInClassInverse name expsQ = do
  info <- reify name
  (_, _, ty) <- decomposeForallT <$> case info of
    VarI _ ty' _     -> return ty'
    ClassOpI _ ty' _ -> return ty'
    _                -> fail $ show name ++ " is no function or class method."
  let originalArity = arrowArity ty
  -- TODO check arity
  exps <- sequence expsQ
  mapping <- makeFreeMap (createIDMapping exps)
  let liftedName = liftTHName name
  argExps <- mapM (convertExp (map (second fst) mapping)) exps
  funPatExp <- genLiftedApply (VarE liftedName) argExps
  resName <- newName "res"
  let invArgPats = [resName]
      matchExp = applyExp (VarE 'matchFL) [VarE resName, funPatExp]
      freeExps = map (VarE . fst . snd) mapping
      letExp = DoE [LetS (map (snd . snd) mapping), NoBindS matchExp, NoBindS returnExp ]
      returnExp = mkLiftedTupleE freeExps





      searchFunNm = 'bfs

      bodyExp = applyExp (VarE 'map) [VarE (if False {-nonGround-} then 'fromEither else 'fromIdentity), AppE (VarE searchFunNm) (applyExp (VarE 'evalWith)
        [ VarE (if False {-nonGround-} then 'normalFormFL else 'groundNormalFormFL)
        , letExp])]
  bNm <- newName "b"
  let letDecs = [SigD bNm (ForallT [] [WildCardT] WildCardT), FunD bNm [Clause (map VarP invArgPats) (NormalB bodyExp) []]]
  return $ LetE letDecs (VarE bNm)-}

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
                    | otherwise -> error "wrong form of input class"
            | otherwise   -> fail "forbidden function application in input/output specification of an inverse" --TODO
    _ -> AppE <$> convertExp freeMap exp' <*> convertExp freeMap exp2
  ParensE exp' -> ParensE <$> convertExp freeMap exp'
  InfixE m_exp exp' ma | isJust m_exp && isJust ma -> convertExp freeMap (applyExp exp' (map fromJust [m_exp, ma]))
  TupE m_exps | all isJust m_exps -> mkLiftedTupleE <$> mapM (convertExp freeMap . fromJust) m_exps
  ListE exps -> convertExp freeMap (foldr (\x xs -> applyExp (ConE '(:)) [x, xs]) (ConE '[]) exps)
  UnboundVarE na -> fail $ "Variable not in scope: " ++ show na --TODO: fail
  e -> fail $ "unsupported syntax in convertExp: " ++ show e
  where
    createLambda name ty = do
      let (_, _, ty') = decomposeForallT ty
          argsNum = arrowArity ty'
      nms <- replicateM argsNum (newName "arg")
      return $ LamE (map VarP nms) (AppE (VarE 'return) (foldl AppE (ConE (liftTHName name)) (map VarE nms)))
  {- TODO

  RecConE na x0 -> _
  ArithSeqE ra -> _
  AppTypeE exp' ty -> _
  SigE exp' ty -> _

  UInfixE exp' exp2 exp3 -> _
  LamE pats exp' -> _
  LamCaseE mas -> _
  UnboxedTupE m_exps -> _
  UnboxedSumE exp' n i -> _
  CondE exp' exp2 exp3 -> _
  MultiIfE x0 -> _
  LetE decs exp' -> _
  CaseE exp' mas -> _
  DoE sts -> _
  MDoE sts -> _
  CompE sts -> _
  RecUpdE exp' x0 -> _
  StaticE exp' -> _
  LabelE s -> _
  ImplicitParamVarE s -> _-}

-- let x = ... :: _1
--     y = ... :: _1

-- f free1 free2 = (..)
-- f (free 1) (free 2)

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

renameWithFresh :: Type -> Type
renameWithFresh = go Map.empty freshVars
  where
    freshVars = [mkName str | str <- [[c] | c <- ['a' .. 'z']] ++ [c : show n | c <- ['a' .. 'z'], n <- [(0 :: Int) ..]]]

    binderName (PlainTV  n  ) = n
    binderName (KindedTV n _) = n

    lookupOrKeep n m = fromMaybe n (Map.lookup n m)

    go m fresh (ForallT vs ctxt ty) =
      let m' = foldr (uncurry Map.insert) m $ zipWith (\a b -> (binderName a, b)) vs fresh
      in ForallT (map (goTV m' fresh) vs) (map (go m' fresh) ctxt) (go m' fresh ty)
    go m _ (VarT n) = VarT (lookupOrKeep n m)
    go m fresh (AppT     ty1 ty2) = AppT (go m fresh ty1) (go m fresh ty2)
    go m fresh (SigT     ty1 ty2) = SigT (go m fresh ty1) (go m fresh ty2)
    go m fresh (AppKindT ty1 ty2) = AppKindT (go m fresh ty1) (go m fresh ty2)
    go m fresh (InfixT  ty1 n ty2) = InfixT (go m fresh ty1) (lookupOrKeep n m) (go m fresh ty2)
    go m fresh (UInfixT ty1 n ty2) = UInfixT (go m fresh ty1) (lookupOrKeep n m) (go m fresh ty2)
    go m fresh (ParensT ty) = ParensT (go m fresh ty)
    go m fresh (ImplicitParamT s ty) = ImplicitParamT s (go m fresh ty)
    go _ _ ty = ty

    goTV m _ (PlainTV n) = PlainTV (lookupOrKeep n m)
    goTV m fresh (KindedTV n ty) = KindedTV (lookupOrKeep n m) (go m fresh ty)

genInverse :: String -> Type -> [Int] -> Bool -> Name -> DecsQ
genInverse originalString originalTy fixedArgs nonGround liftedName = do
  let invName = mkInverseName originalString fixedArgs nonGround
      (originalTyVarBndrs, originalCxt, originalTy') = decomposeForallT (renameWithFresh originalTy)
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





            searchFunNm = 'bfs

            bodyExp = applyExp (VarE 'map) [VarE (if nonGround then 'fromEither else 'fromIdentity), AppE (VarE searchFunNm) (applyExp (VarE 'evalWith)
              [ VarE (if nonGround then 'normalFormFL else 'groundNormalFormFL)
              , applyExp (VarE '(>>)) [matchExp, returnExp]])]
            body = NormalB bodyExp
        return $ FunD invName [Clause invArgPats body []]

  sequence [genPartialInverseSig, genPartialInverseFun]

--mkLiftedList :: [Exp] -> Exp
--mkLiftedList = foldr (AppE (ConE 'ConsFL)

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

      genInvertible = do
        let ctxt = [ mkConvertibleConstraint originalTy
                   , mkMatchableConstraint originalTy
                   , mkNormalFormConstraint originalTy
                   , mkHasPrimitiveInfoConstraint (mkLifted (ConT ''FL) originalTy)
                   ] ++ map mkInvertibleConstraint originalConArgs
        return $ InstanceD Nothing ctxt (mkInvertibleConstraint originalTy) [] :: Q Dec

  (++) <$> genLifted originalTc liftedTc liftedTyVars mTy
       <*> sequence [genHasPrimitiveInfo, genNarrowable, genConvertible, genMatchable, genNormalForm, genInvertible]

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

mkNormalFormConstraint :: Type -> Type
mkNormalFormConstraint ty = applyType (ConT ''NormalForm) [ty]

mkInvertibleConstraint :: Type -> Type
mkInvertibleConstraint ty = applyType (ConT ''Invertible) [ty]
