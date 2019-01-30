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
-- There is also a README in the test/samples directory where the C
-- source is described, along with various tests.

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Main ( main ) where

import           GHC.TypeLits

import           Control.Lens hiding ( (<.>) )
import           Control.Monad
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as E
import           Data.Foldable
import           Data.Function ( on )
import           Data.List ( intercalate, sortBy )
import qualified Data.Macaw.Architecture.Info as AI
import           Data.Macaw.BinaryLoader as MBL
import           Data.Macaw.BinaryLoader.X86 ()
import           Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory.ElfLoader as ML
import           Data.Macaw.PPC
import           Data.Macaw.Refinement
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.X86 as MX86
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import           Data.Parameterized.Some
import           Data.Proxy
import           Data.Semigroup ( (<>) )
import qualified Data.Set as Set
import           Data.Tagged
import           Data.Typeable ( Typeable )
import           Options.Applicative
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import           System.Directory ( doesFileExist )
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath as FP
import qualified System.FilePath.Glob as FPG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import           Test.Tasty.Ingredients
import           Test.Tasty.Options
import           Text.PrettyPrint.ANSI.Leijen hiding ( (<$>), (<>), (</>) )
import           Text.Read ( readEither )

import           Prelude


datadir =  "tests/samples"
supportedArch = [ "x86"
                , "ppc"
                ]


data ShowSearch =  ShowSearch Bool deriving (Eq, Ord, Typeable)

instance IsOption ShowSearch where
  defaultValue = ShowSearch False
  parseValue = fmap ShowSearch . safeRead
  optionName = pure $ "showsearch"
  optionHelp = pure $ "Show details of the search for the set of\n\
                      \refinement tests that would be performed\n\
                      \based on the contents of the " <> datadir <> " directory"
  optionCLParser = ShowSearch <$> switch
                      ( long (untag (optionName :: Tagged ShowSearch String))
                      <> help (untag (optionHelp :: Tagged ShowSearch String))
                      )

data VerboseLogging = VerboseLogging Bool
  deriving (Eq, Ord)

instance IsOption VerboseLogging where
  defaultValue = VerboseLogging False
  parseValue = fmap VerboseLogging . safeRead
  optionName = pure "verbose-logging"
  optionHelp = pure "Turn on verbose logging output"
  optionCLParser = VerboseLogging <$> switch ( long (untag (optionName :: Tagged VerboseLogging String))
                                             <> help (untag (optionHelp :: Tagged VerboseLogging String))
                                             )


-- | This is a Tasty "Ingredient" (aka test runner) that can be used
-- to display the search process and results for generating the tests.
searchResultsReport = TestManager [] $ \opts _tests ->
  if lookupOption opts == ShowSearch True
  then Just $ do searchlist <- getTestList datadir True
                 putStrLn ""
                 putStrLn $ "Final set of tests [" ++ show (length searchlist) ++ "]:"
                 mapM_ (putStrLn . show) searchlist
                 return True
  else Nothing


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
  testInputs <- getTestList datadir False
  let testNames = Set.fromList $ map name testInputs
  TT.defaultMainWithIngredients ingredients $
    TT.testGroup "macaw-refinement" $
    mkNameGroup testInputs <$> toList testNames
  where mkNameGroup inps nm =
          TT.testGroup nm $ map mkTest $ filter ((==) nm . name) inps


data TestInput = TestInput { name :: String
                           , arch :: String
                           , expectFileBase :: Maybe FilePath
                           , expectFileRefined :: Maybe FilePath
                           , binaryFile :: FilePath
                           }
  deriving (Eq,Show)

-- | Returns a list of the TestInputs that should be run.  These are
-- driven by the existence of a .[F-]expected file, for which there
-- should be a corresponding .exe.  The exe and expected files are
-- sub-named by the architecture (A) to which they apply.
getTestList :: FilePath -> Bool -> IO [TestInput]
getTestList basedir explain = do
  when explain $ putStrLn $ "Checking for test inputs in " <> (basedir </> "*.exe")
  let exeGlob = "*.(" <> (intercalate "|" supportedArch) <> ").exe"
  exeNames <- FPG.namesMatching $ basedir </> exeGlob
  postproc <$> mapM mkTI exeNames
  where
    postproc = sorted . catMaybes
    sorted = sortBy (compare `on` name)
    mkTI exe = do when explain $ putStrLn $ "Checking exe " ++ exe
                  -- exe is path/to/srcfile.A.exe
                  let exeRmvd = fst $ FP.splitExtension exe
                      (srcPathAndName, testArch') = FP.splitExtension exeRmvd
                      testName = FP.takeFileName srcPathAndName
                  if length testArch' < 2
                    then do when explain $ putStrLn $ "  no arch, skipping"
                            return Nothing
                    else mkTIAN exe (drop 1 testArch') testName
    mkTIAN exe testArch testName = do
          when explain $ putStrLn $ "  arch = " <> testArch
          when explain $ putStrLn $ "  name = " <> testName
          let expRoot = basedir </> testName <.> testArch
              expBaseName = expRoot <.> "base-expected"
              expRefinedName = expRoot <.> "refined-expected"
              expName = expRoot <.> "expected"
          base <- doesFileExist expBaseName
          refn <- doesFileExist expRefinedName
          expt <- doesFileExist expName
          let expn = if expt then Just expName else Nothing
          mkTIANE exe testArch testName
            (if base then Just expBaseName else expn)
            (if refn then Just expRefinedName else expn)
    mkTIANE exe testArch testName expBase expRefn = do
      when explain $ case expBase of
                       Just f -> putStrLn $ "  expected base = " <> f
                       Nothing -> return ()
      when explain $ case expRefn of
                       Just f -> putStrLn $ "  expected refined = " <> f
                       Nothing -> return ()
      case (expBase, expRefn) of
        (Nothing, Nothing) -> return Nothing
        _ -> return $ Just $ TestInput { name = testName
                                       , arch = testArch
                                       , binaryFile = exe
                                       , expectFileBase = expBase
                                       , expectFileRefined = expRefn
                                       }


mkTest :: TestInput -> TT.TestTree
mkTest testinp =
  let readbin = BS.readFile $ binaryFile testinp
      cleanup = return . const ()
      formName ref = if ref then "refined" else "base"
      tests = catMaybes [ mkT False <$> expectFileBase testinp
                        , mkT True <$> expectFileRefined testinp
                        ]
      mkT ref fn = \v r -> TTH.testCase (formName ref) $
                           testExpected ref fn testinp v r
  in TT.askOption $ \(VerboseLogging beVerbose) ->
     TT.withResource readbin cleanup $
     \readBinary ->
       TT.testGroup (arch testinp) $ map (\t -> t beVerbose readBinary) tests


testExpected useRefinement expFile testinp beVerbose readBinary = do
  bs <- readBinary
  case E.parseElf bs of
      E.Elf64Res warnings elf -> mapM_ print warnings >> withElf64 elf
      E.Elf32Res warnings elf -> mapM_ print warnings >> withElf32 elf
      _ -> let badMsg = binaryFile testinp <> " is not a 64-bit ELF file"
           in do when beVerbose $ putStrLn badMsg
                 TTH.assertBool badMsg False
  where
    withElf64 elf =
      case E.elfMachine elf of
        E.EM_PPC64 -> do
          bin <- MBL.loadBinary @PPC64.PPC ML.defaultLoadOptions elf
          let pli = ppc64_linux_info bin
          withBinaryDiscoveredInfo testinp useRefinement expFile pli bin
        E.EM_X86_64 ->
          withBinaryDiscoveredInfo testinp useRefinement expFile MX86.x86_64_linux_info =<<
            MBL.loadBinary @MX86.X86_64 ML.defaultLoadOptions elf
        m -> error $ "no 64-bit ELF support for " ++ show m
    withElf32 elf =
      case E.elfMachine elf of
        E.EM_PPC -> do
          bin <- MBL.loadBinary @PPC32.PPC ML.defaultLoadOptions elf
          let pli = ppc32_linux_info bin
          withBinaryDiscoveredInfo testinp useRefinement expFile pli bin
        m -> error $ "no 32-bit ELF support for " ++ show m

withBinaryDiscoveredInfo :: ( X.MonadThrow m
                            , MS.SymArchConstraints arch
                            , 16 <= MC.ArchAddrWidth arch
                            , MBL.BinaryLoader arch binFmt
                            , MonadIO m) =>
                            TestInput
                         -> Bool
                         -> FilePath
                         -> AI.ArchitectureInfo arch
                         -> MBL.LoadedBinary arch binFmt
                         -> m ()
withBinaryDiscoveredInfo testinp useRefinement expFile arch_info bin = do
  entries <- toList <$> entryPoints bin
  let baseCFG = MD.cfgFromAddrs arch_info (memoryImage bin) M.empty entries []
      actualBase = cfgToExpected testinp bin (Just baseCFG) Nothing
  refinedCFG <- refineDiscovery baseCFG
  let refinedBase = cfgToExpected testinp bin Nothing (Just refinedCFG)
      formName = if useRefinement then "refined" else "base"
      actual = if useRefinement then refinedBase else actualBase
  compareToExpected formName actual expFile


compareToExpected formName actual fn =
  let cfgName = formName <> " CFG" in
  do expectedData <- liftIO $ readFile fn
     case readEither expectedData of
       Right expInfo ->
         -- KWQ: TODO: refine this down to individual components if it fails
         liftIO $ TTH.assertEqual ("discovered " <> cfgName) expInfo actual
       Left e ->
         let badMsg = "error parsing expected " <> cfgName <> " data in " <> fn <> ": " <> e
             outFileName = take (length fn - length "expected") fn <> "last-actual"
         in liftIO $ do writeFile outFileName $ show actual
                        putStrLn $ "Generated actual output to: " <> outFileName
                        TTH.assertBool badMsg False

----------------------------------------------------------------------

-- | The ExpectedInfo is the format of information stored in the
-- .expected files.  Ideally this would be a 'Show' output so that a
-- 'Read' could import native data structures for a more refined
-- comparison, but unfortunately the 'read . show == id' intent is not
-- held for Macaw/Flexdis86, so the actual stored and compared format
-- is generally the 'pretty' output of the structures.
data ExpectedInfo arch = Expected
  { expBinaryName  :: String
  , expEntryPoints :: [EntryPoint arch]
  , expFunctions   :: [Function arch]
  }
  deriving (Show, Read, Eq)

data EntryPoint arch = EntryPoint (Address arch)
  deriving (Show, Read, Eq)

data Function arch = Function (Address arch) [Block arch]
  deriving (Show, Read, Eq)

data Block arch = Block (Address arch) StatementList
  deriving (Show, Read, Eq)

data Address arch = Address { addrSegmentBase :: Int
                            , addrSegmentOffset :: Int
                            , addrSegoffOffset :: Int
                            , addrPretty :: String
                            }
  deriving (Show, Read, Eq)

mkAddress :: (MemWidth (RegAddrWidth (ArchReg arch))) =>
             MC.MemSegmentOff (MC.ArchAddrWidth arch) -> Address arch
mkAddress addr = Address { addrSegmentBase = fromEnum $ segmentBase $ segoffSegment addr
                         , addrSegmentOffset = fromEnum $ memWordToUnsigned $ segmentOffset $ segoffSegment addr
                         , addrSegoffOffset = fromEnum $ memWordToUnsigned $ segoffOffset addr
                         , addrPretty = show $ pretty addr
                         }

type StatementList = String  -- no Read or Eq for Macaw.Discovery.StatementList, so just use String format

cfgToExpected :: (MBL.BinaryLoader arch binFmt) =>
                 TestInput
              -> MBL.LoadedBinary arch binFmt
              -> Maybe (MD.DiscoveryState arch)
              -> Maybe (MD.DiscoveryState arch)
              -> ExpectedInfo arch
cfgToExpected testinp bin mbCFG mbRefCFG =
  let eps = case entryPoints bin of
              Left _ -> []
              Right epl -> toList epl
      fns = case (mbCFG, mbRefCFG) of
              (Nothing, Nothing) -> error "must specify a discovered Macaw CFG"
              (Just _, Just _) -> error "must specify only one discovered Macaw CFG"
              (Just di, Nothing) -> getFunctions di
              (Nothing, Just di) -> getFunctions di
  in Expected { expBinaryName = binaryFile testinp
              , expEntryPoints = (EntryPoint . mkAddress) <$> eps
              , expFunctions = fns
              }

getFunctions :: MD.DiscoveryState arch -> [Function arch]
getFunctions di =
  AI.withArchConstraints (MD.archInfo di) $
  fmap (\(funAddr, Some dfi) ->
           Function
           (mkAddress funAddr)
           (fmap (\(blkAddr, pb) ->
                    Block (mkAddress blkAddr) (show $ MD.blockStatementList pb))
            (dfi ^. MD.parsedBlocks . to M.toList)))
  (di ^. MD.funInfo . to M.toList)
