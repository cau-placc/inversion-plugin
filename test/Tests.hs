{-# LANGUAGE LambdaCase #-}
module Tests (tests) where

import Test.QuickCheck
import Distribution.TestSuite
import System.Directory
import System.Process
import System.Exit
import System.Environment

import SemanticTests

tests :: IO [Test]
tests = do
  path <- makeAbsolute "test-examples"
  setCurrentDirectory  path
  args' <- getArgs
  let args = if null args' then ["Semantic", "Compile"] else args'
  return
    [ if "Compile" `notElem` args then noTest else testGroup "Compile Tests"
    [ Test (mkCompileTest Succeed    "Data.hs")
    , Test (mkCompileTest Succeed    "Import.hs")
    , Test (mkCompileTest ExpectFail "ImportHaskell.hs")
    , Test (mkCompileTest Succeed    "InstanceImport.hs")
    , Test (mkCompileTest Succeed    "PatternMatching.hs")
    , Test (mkCompileTest Succeed    "Record.hs")
    , Test (mkCompileTest Succeed    "Typeclass.hs")
    ]
    , if "Semantic" `notElem` args then noTest else testGroup "Semantic Tests"
    [ Test (mkSemanticQuickCheck is42Test "is42Test")
    , Test (mkSemanticQuickCheck lastTest "lastTest")
    , Test (mkSemanticQuickCheck lookupTestReverse "lookupTestReverse")
    , Test (mkSemanticQuickCheck lookupTestUnused "lookupTestUnused")
    ]
    ]
  where noTest = testGroup "Empty Group" []

data Expected = Succeed | ExpectFail

mkCompileTest :: Expected -> FilePath -> TestInstance
mkCompileTest expect file = TestInstance
  { run = testGhcInvocation expect file
  , name = file
  , tags = ["Compile"]
  , options = []
  , setOption = \_ _ -> Left "Option not supported"
  }

mkSemanticQuickCheck :: Testable a => a -> String -> TestInstance
mkSemanticQuickCheck test testName = TestInstance
  { run = mkQuickCheckTest test
  , name = testName
  , tags = ["Semantic"]
  , options = []
  , setOption = \_ _ -> Left "Option not supported"
  }

mkQuickCheckTest :: Testable a => a -> IO Progress
mkQuickCheckTest test = quickCheckResult test >>= \case
  Success {} -> return (Finished Pass)
  other      -> return (Finished (Fail (output other)))

testGhcInvocation :: Expected -> FilePath -> IO Progress
testGhcInvocation expect file = do
  process <- spawnProcess "ghc"
    ["-hidir out", "-odir out", "-fforce-recomp", "-dcore-lint", file]
  code <- waitForProcess process
  return $ case code of
    ExitSuccess   | Succeed    <- expect
      -> Finished Pass
    ExitSuccess   | ExpectFail <- expect
      -> Finished (Fail "Compilation succeeded, but was expected to fail")
    ExitFailure _ | ExpectFail <- expect
      -> Finished Pass
    ExitFailure _ | Succeed    <- expect
      -> Finished (Fail "Compilation failed unexpectedly")
