-- This test harness uses local files to run Macaw discovery both with
-- and without refinement and checks the results of that validation
-- against expected outputs (aka. golden testing).
--
-- test/samples/
--    X[.A].[F-]expected       -- expected (golden) output [the primary file that enables this test]
--    X.A.exe                  -- input ELF binary file
--    X.c                      -- C source for generating binary
--
-- This methodology allows a binary for each architecture (A) to be
-- produced from a single C source (X), and then one or more
-- refinement test forms (F) to be created to run on that binary,
-- where F is one of:
--
--    "base"    -- standard Macaw discovery
--    "refined" -- additional discovery from this macaw-refinement package
--
-- If there is no "F-" portion, then the same expected file is applied
-- for all possible values of F.
--
-- If there is an expected file but it fails to Parse on a Haskell
-- Read (e.g. "echo garbage > blah.ppc.base-expected") then the test
-- will write the actual output to a separate file with the
-- "last-actual" suffix (e.g. "blah.ppc.base-last-actual"); verify the
-- contents of that file and then simply copy them to the expected
-- file to get the correct file contents.
--
-- There is also a README in the test/samples directory where the C
-- source is described, along with various tests.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Main ( main ) where

import           Control.Monad ( when )
import qualified Data.Foldable as F
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Refinement as MR
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MSM
import qualified Data.Macaw.Types as MT
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as Set
import qualified Data.Tagged as DT
import qualified Data.Text as T
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import           Options.Applicative
import qualified System.Directory as SD
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath.Glob as FPG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import           Test.Tasty.Ingredients as TI
import           Test.Tasty.Options
import           Text.Printf ( printf )
import           Text.Read ( readEither )
import qualified What4.ProgramLoc as WPL
import qualified What4.BaseTypes as WT
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI

import           Prelude

import           Initialization ( withElf, withRefinedDiscovery )
import           Summary ( blockAddresses )
import           Options ( Options(..) )

datadir :: FilePath
datadir =  "tests/samples"

data ShowSearch =  ShowSearch Bool deriving (Eq, Ord, Typeable)

instance IsOption ShowSearch where
  defaultValue = ShowSearch False
  parseValue = fmap ShowSearch . safeRead
  optionName = pure $ "showsearch"
  optionHelp = pure $ "Show details of the search for the set of\n\
                      \refinement tests that would be performed\n\
                      \based on the contents of the " <> datadir <> " directory"
  optionCLParser = ShowSearch <$> switch
                      ( long (DT.untag (optionName :: DT.Tagged ShowSearch String))
                      <> help (DT.untag (optionHelp :: DT.Tagged ShowSearch String))
                      )

data VerboseLogging = VerboseLogging Bool
  deriving (Eq, Ord)

instance IsOption VerboseLogging where
  defaultValue = VerboseLogging False
  parseValue = fmap VerboseLogging . safeRead
  optionName = pure "verbose-logging"
  optionHelp = pure "Turn on verbose logging output"
  optionCLParser = VerboseLogging <$> switch ( long (DT.untag (optionName :: DT.Tagged VerboseLogging String))
                                             <> help (DT.untag (optionHelp :: DT.Tagged VerboseLogging String))
                                             )


-- | This is a Tasty "Ingredient" (aka test runner) that can be used
-- to display the search process and results for generating the tests.
searchResultsReport :: TI.Ingredient
searchResultsReport = TestManager [] $ \opts _tests ->
  if lookupOption opts == ShowSearch True
  then Just $ do searchlist <- getConcreteTestList datadir True
                 putStrLn ""
                 putStrLn $ "Final set of tests [" ++ show (length searchlist) ++ "]:"
                 mapM_ (putStrLn . show) searchlist
                 putStrLn ""
                 putStrLn ("These search results were based on the contents of the " <>
                           datadir <> " directory\n\
                           \Syntax:  BASENAME.c\n\
                           \         BASENAME.exe\n\
                           \         BASENAME.exe.expected\n\
                           \Note that if any .expected file fails a Haskell Read\n\
                           \parse, a \".....last-actual\" file is written; it can\n\
                           \be verified and renamed to be the new expected contents.\n")

                 return True
  else Nothing


ingredients :: [TI.Ingredient]
ingredients = TT.includingOptions [ Option (Proxy :: Proxy ShowSearch)
                                  , Option (Proxy :: Proxy VerboseLogging)
                                  ]
              : searchResultsReport
              : TT.defaultIngredients

main :: IO ()
main = do
  -- Note: dynamic test generation should be done before the
  -- TT.defaultMain call, but test arguments/options are not yet
  -- available for this; see:
  -- https://stackoverflow.com/questions/33040722
  -- https://github.com/feuerbach/tasty/issues/228
  concreteTestInputs <- getConcreteTestList datadir False
  symbolicTestInputs <- getSymbolicTestList datadir False
  -- let testNames = Set.fromList (map name testInputs)
  let ?memOpts = CLM.defaultMemOptions
  let tests = concat [ map mkTest concreteTestInputs
                     , map mkSymbolicTest symbolicTestInputs
                     ]
  TT.defaultMainWithIngredients ingredients $
    TT.testGroup "macaw-refinement" tests

data TestInput = TestInput { binaryFilePath :: FilePath
                           , expectedFilePath :: FilePath
                           }
               deriving (Eq, Show)

-- | Returns a list of the TestInputs that should be run.  These are
-- driven by the existence of a .[F-]expected file, for which there
-- should be a corresponding .exe.  The exe and expected files are
-- sub-named by the architecture (A) to which they apply.
getConcreteTestList :: FilePath -> Bool -> IO [TestInput]
getConcreteTestList basedir explain = do
  when explain $ putStrLn $ "Checking for test inputs in " <> (basedir </> "*.exe")

  -- Find all of the executables we have available
  exeNames <- FPG.namesMatching (basedir </> "*.exe")

  -- For each executable, produce a TestInput iff it has an associated .expected file
  catMaybes <$> mapM findExpectedFiles exeNames
  where
    findExpectedFiles exeName = do
      let expectedFilename = exeName <.> "expected"
      SD.doesFileExist expectedFilename >>= \case
        True -> return $ Just TestInput { binaryFilePath = exeName
                                        , expectedFilePath = expectedFilename
                                        }
        False -> return Nothing

getSymbolicTestList :: FilePath -> Bool -> IO [TestInput]
getSymbolicTestList basedir explain = do
  when explain $ putStrLn ("Checking for symbolic test inputs in " <> (basedir </> "*.symex"))
  exeNames <- FPG.namesMatching (basedir </> "*.exe")
  catMaybes <$> mapM findExpectedFiles exeNames
  where
    findExpectedFiles exeName = do
      let expected = exeName <.> "symex"
      SD.doesFileExist expected >>= \case
        True -> return $ Just TestInput { binaryFilePath = exeName
                                        , expectedFilePath = expected
                                        }
        False -> return Nothing

-- Refinement configuration for the test suite
testOptions :: Bool -> FilePath -> Options
testOptions verb file = Options { inputFile = file
                                , unrefined = False
                                , summaryOnly = False
                                , verbose = verb
                                , solver = MR.Yices
                                , solverInteractionFile = Nothing
                                , maximumModelCount = 20
                                , threadCount = 1
                                , timeoutSeconds = 60
                                }

-- | Test that macaw-refinement can find all of the expected jump targets
--
-- Jump targets are provided in .expected files that are 'read' in.
mkTest :: (?memOpts :: CLM.MemOptions) => TestInput -> TT.TestTree
mkTest testinp = do
  TT.askOption $ \(VerboseLogging beVerbose) -> TTH.testCase (binaryFilePath testinp) $ do
    let opts = testOptions beVerbose (binaryFilePath testinp)
    withElf opts $ \_ archInfo bin _unrefinedDI -> do
      withRefinedDiscovery opts archInfo bin $ \refinedDI _refinedInfo -> do
        let actual = blockAddresses refinedDI
        expectedInput <- readFile (expectedFilePath testinp)
        case readEither expectedInput of
          Left err -> TTH.assertFailure (printf "Failed to parse expected input file [%s]: %s" (expectedFilePath testinp) err)
          Right (expected :: [(Word64, [Word64])]) -> do
            -- We iterate over the *expected* functions so that we can just
            -- specify expected results for interesting bits and ignore the
            -- other discovered functions.
            F.forM_ expected $ \(faddr, expectedBlockAddrs) -> do
              let expectedAddrSet = Set.fromList expectedBlockAddrs
              case M.lookup faddr actual of
                Nothing -> TTH.assertFailure (printf "Missing expected function at address 0x%x" faddr)
                Just actualBlockAddrs -> do
                  F.forM_ expectedBlockAddrs $ \expectedBlockAddr -> do
                    let msg = printf "Missing expected block at 0x%x in function 0x%x" expectedBlockAddr faddr
                    TTH.assertBool msg (Set.member expectedBlockAddr actualBlockAddrs)
                  F.forM_ actualBlockAddrs $ \actualBlockAddr -> do
                    let msg = printf "Found an unexpected block in the binary at 0x%x in function 0x%x" actualBlockAddr faddr
                    TTH.assertBool msg (Set.member actualBlockAddr expectedAddrSet)

posFn :: (MC.MemWidth (MC.ArchAddrWidth arch)) => proxy arch -> MC.MemSegmentOff (MC.ArchAddrWidth arch) -> WPL.Position
posFn _ = WPL.OtherPos . T.pack . show

-- | This test is similar to 'mkTest', but instead of checking the set of
-- recovered blocks, it translates the function into Crucible using
-- macaw-symbolic and symbolically executes it.
--
-- This test is fairly simple in that it isn't checking any interesting
-- property, but only that the simulator does not error out due to unresolved
-- control flow.
mkSymbolicTest :: (?memOpts :: CLM.MemOptions) => TestInput -> TT.TestTree
mkSymbolicTest testinp = do
  TT.askOption $ \(VerboseLogging beVerbose) -> TTH.testCase (binaryFilePath testinp) $ do
    let opts = testOptions beVerbose (binaryFilePath testinp)
    halloc <- CFH.newHandleAllocator
    Some gen <- PN.newIONonceGenerator
    sym <- CBS.newSimpleBackend CBS.FloatRealRepr gen
    expectedInput <- readFile (expectedFilePath testinp)
    let symExecFuncAddrs :: Set.Set Word64
        Right symExecFuncAddrs = Set.fromList <$> readEither expectedInput
    withElf opts $ \proxy archInfo bin _unrefinedDI -> do
      withRefinedDiscovery opts archInfo bin $ \refinedDI _refinedInfo -> do
        let Just archVals = MS.archVals proxy
        let archFns = MS.archFunctions archVals
        let mem = MBL.memoryImage bin
        F.forM_ (MD.exploredFunctions refinedDI) $ \(Some dfi) -> do
          let Just funcAddr = fromIntegral <$> MM.segoffAsAbsoluteAddr (MD.discoveredFunAddr dfi)
          case Set.member funcAddr symExecFuncAddrs of
            False -> return ()
            True -> do
              let funcName = WF.functionNameFromText (T.pack ("target@" ++ show (MD.discoveredFunAddr dfi)))
              printf "External resolutions of %s: %s\n" (show funcName) (show (MD.discoveredClassifyFailureResolutions dfi))
              CCC.SomeCFG cfg <- MS.mkFunCFG archFns halloc funcName (posFn proxy) dfi
              regs <- MS.macawAssignToCrucM (mkReg archFns sym) (MS.crucGenRegAssignment archFns)
              let ?recordLLVMAnnotation = \_ _ -> pure ()
              -- FIXME: We probably need to pull endianness from somewhere else
              (initMem, memPtrTbl) <- MSM.newGlobalMemory proxy sym CLD.LittleEndian MSM.ConcreteMutable mem
              let globalMap = MSM.mapRegionPointers memPtrTbl
              let lookupFn = MS.unsupportedFunctionCalls "macaw-refinement-tests"
              let lookupSC = MS.unsupportedSyscalls "macaw-refinement-tests"
              let validityCheck _ _ _ _ = return Nothing
              MS.withArchEval archVals sym $ \archEvalFns -> do
                (_, res) <- MS.runCodeBlock sym archFns archEvalFns halloc (initMem, globalMap) lookupFn lookupSC validityCheck cfg regs
                case res of
                  CS.FinishedResult _ (CS.TotalRes _) -> return ()
                  CS.FinishedResult _ (CS.PartialRes {}) -> return ()
                  CS.AbortedResult _ ares ->
                    case ares of
                      CS.AbortedExec rsn _ -> TTH.assertFailure ("Symbolic execution aborted: " ++ show rsn)
                      CS.AbortedExit {} -> TTH.assertFailure "Symbolic execution exited"
                      CS.AbortedBranch {} -> return ()
                  CS.TimeoutResult {} -> TTH.assertFailure "Symbolic execution timed out"

-- | Allocate a fresh value for a machine register
--
-- Only Bool and BV types are supported
mkReg :: (CB.IsSymInterface sym, MT.HasRepr (MC.ArchReg arch) MT.TypeRepr)
      => MS.MacawSymbolicArchFunctions arch
      -> sym
      -> MC.ArchReg arch tp
      -> IO (CS.RegValue' sym (MS.ToCrucibleType tp))
mkReg archFns sym r =
  case MT.typeRepr r of
    MT.BoolTypeRepr ->
      CS.RV <$> WI.freshConstant sym (MS.crucGenArchRegName archFns r) WT.BaseBoolRepr
    MT.BVTypeRepr w ->
      CS.RV <$> (CLM.llvmPointer_bv sym =<< WI.freshConstant sym (MS.crucGenArchRegName archFns r) (WT.BaseBVRepr w))
    MT.TupleTypeRepr{}  ->
      error "macaw-symbolic do not support tuple types."
    MT.FloatTypeRepr{}  ->
      error "macaw-symbolic do not support float types."
    MT.VecTypeRepr{}  ->
      error "macaw-symbolic do not support vector types."
