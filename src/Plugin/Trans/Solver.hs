{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Plugin.Trans.Solver where

import GHC.TcPlugin.API
import GHC.TcPlugin.API.Internal
import GHC.Tc.Types.Constraint
import GHC.Core as Core

import Plugin.Trans.Type
import Plugin.Effect.Monad
import GHC.Builtin.Types
import GHC.Core.TyCo.Rep

solveShareableAnyPlugin :: TcPlugin
solveShareableAnyPlugin = TcPlugin {
    tcPluginInit = createAltPredType,
    tcPluginSolve = solveShareAny,
    tcPluginRewrite = const emptyUFM,
    tcPluginStop = \_ -> return ()
  }

solveShareAny :: PredType -> TcPluginSolver
solveShareAny pty' _ wanteds = do
  uncurry TcPluginOk . concatBoth . unzip <$> mapM trySolveWanted wanteds
  where
    concatBoth (x, y) = (concat x, concat y)
    trySolveWanted :: Ct -> TcPluginM 'Solve ([(EvTerm, Ct)], [Ct])
    trySolveWanted (CQuantCan _) = return ([], [])
    trySolveWanted ct@(cc_ev -> CtWanted pty _ si loc) = do
      stycon <- unsafeLiftTcM getShareClassTycon
      case splitTyConApp_maybe pty of
        Just (tycon, [_, arg])
          | tycon == stycon &&
            arg `eqType` anyTypeOfKind liftedTypeKind -> do
              v <- newEvVar pty'
              let newW = CtWanted pty' (EvVarDest v) si loc
              let co = mkUnivCo (PluginProv "Shareable for Any") Representational pty' pty
              return ([(evCast (Core.Var v) co, ct)], [CNonCanonical newW])
        _ -> return ([], [])
    trySolveWanted _ = return ([], [])

createAltPredType :: TcPluginM 'Init Type
createAltPredType = do
  stycon <- unsafeLiftTcM getShareClassTycon
  mtycon <- unsafeLiftTcM getMonadTycon
  atycon <- unsafeLiftTcM $ getTyCon "Plugin.BuiltIn" "Anything"
  return $ mkTyConApp stycon [mkTyConTy mtycon, mkTyConTy atycon]
