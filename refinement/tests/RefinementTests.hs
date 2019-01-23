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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Main ( main ) where

import           Control.Lens hiding ( (<.>) )
import           Control.Monad
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as E
import           Data.Foldable
import           Data.Function ( on )
import           Data.List ( sortBy )
import qualified Data.Macaw.Architecture.Info as AI
import           Data.Macaw.BinaryLoader as MBL
import           Data.Macaw.BinaryLoader.X86 ()
import           Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory.ElfLoader as ML
import           Data.Macaw.PPC
import qualified Data.Macaw.X86 as MX86
import qualified Data.Map as M
import           Data.Maybe ( catMaybes )
import           Data.Parameterized.Some
import           Data.Proxy
import           Data.Semigroup ( (<>) )
import           Data.Tagged
import           Data.Typeable ( Typeable )
import           Options.Applicative
import qualified SemMC.Architecture.PPC64 as PPC64
import           System.Directory ( doesFileExist )
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath as FP
import qualified System.FilePath.Glob as FPG
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import           Test.Tasty.Options
import           Text.PrettyPrint.ANSI.Leijen hiding ( (<$>), (<>), (</>) )
import           Text.Read ( readEither )

import           Prelude



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

ingredients = TT.includingOptions [ Option (Proxy :: Proxy ShowSearch)
                                  , Option (Proxy :: Proxy VerboseLogging)
                                  ] : TT.defaultIngredients

main :: IO ()
main = do
  testInputs <- getTestList datadir False
  TT.defaultMainWithIngredients ingredients $
    TT.askOption $ \beVerbose ->
    TT.askOption $ \(ShowSearch jl) ->
      if jl
      then TTH.testCase "Test Search" $ do searchlist <- getTestList datadir True
                                           putStrLn ""
                                           putStrLn $ "Final set of tests [" ++ show (length searchlist) ++ "]:"
                                           mapM_ (putStrLn . show) searchlist
      else
        TT.testGroup "macaw-refinement" $ map (mkTestCase beVerbose) testInputs

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
  exeNames <- (FPG.namesMatching $ basedir </> "*exe")
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


mkTestCase :: VerboseLogging -> TestInput -> TT.TestTree
mkTestCase (VerboseLogging beVerbose) testinp =
  TTH.testCase (name testinp) $ do
    bs <- BS.readFile (binaryFile testinp)
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
          withBinaryDiscoveredInfo testinp {- (showDiscoveryInfo testinp) -} pli bin
        E.EM_X86_64 ->
          withBinaryDiscoveredInfo testinp {- (showDiscoveryInfo testinp) -} MX86.x86_64_linux_info =<<
            MBL.loadBinary @MX86.X86_64 ML.defaultLoadOptions elf
        m -> error $ "no 64-bit ELF support for " ++ show m
    withElf32 elf =
      case E.elfMachine elf of
        E.EM_PPC -> do  -- 32 bit
          bin <- MBL.loadBinary @PPC32.PPC ML.defaultLoadOptions elf
          let pli = ppc32_linux_info bin
          withBinaryDiscoveredInfo testinp pli bin
        m -> error $ "no 32-bit ELF support for " ++ show m

withBinaryDiscoveredInfo :: ( X.MonadThrow m
                            , MBL.BinaryLoader arch binFmt
                            , MonadIO m) =>
                            TestInput
                         -- -> (MD.DiscoveryState arch -> m a)
                         -> AI.ArchitectureInfo arch
                         -> MBL.LoadedBinary arch binFmt
                         -> m ()
withBinaryDiscoveredInfo testinp {- f -} arch_info bin = do
  entries <- toList <$> entryPoints bin
  let baseCFG = MD.cfgFromAddrs arch_info (memoryImage bin) M.empty entries []
      actualBase = cfgToExpected testinp bin (Just baseCFG) Nothing
  case expectFileBase testinp of
    Just fn ->
      do expectedData <- liftIO $ readFile fn
         case readEither expectedData of
           Right expInfo ->
             liftIO $ TTH.assertEqual "discovered CFG" expInfo actualBase
           Left e ->
             let badMsg = "error parsing expected base CFG " <> fn <> ": " <> e
                 actFileName = take (length fn - length "expected") fn <> "last-actual"
             in liftIO $ do writeFile actFileName $ show actualBase
                            putStrLn $ "Generated actual output to: " <> actFileName
                            TTH.assertBool badMsg False
    Nothing -> return ()


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
              -> Maybe Int
              -> ExpectedInfo arch
cfgToExpected testinp bin mbCFG mbRefCFG =
  let eps = case entryPoints bin of
              Left _ -> []
              Right epl -> toList epl
      fns = case (mbCFG, mbRefCFG) of
              (Nothing, Nothing) -> error "must specify a discovered Macaw CFG"
              (Just _, Just _) -> error "must specify only one discovered Macaw CFG"
              (Just di, Nothing) -> getFunctions di
              (Nothing, Just _di) -> undefined  -- KWQ: refined
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
