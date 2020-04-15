{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module ARMTests
    ( armAsmTests
    )
    where


import           Control.Lens hiding ( ignored )
import           Control.Monad ( when )
import           Control.Monad.Catch ( throwM, Exception )
import qualified Data.ElfEdit as E
import qualified Data.Foldable as F
import qualified Data.Macaw.ARM as RO
import qualified Data.Macaw.ARM.BinaryFormat.ELF as ARMELF
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import qualified Data.Parameterized.Some as PU
import qualified Data.Set as S
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import           Shared
import           System.FilePath ( dropExtension, replaceExtension )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import           Text.PrettyPrint.ANSI.Leijen ( putDoc )
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

import           Prelude


-- | Set to true to build with chatty output.
isChatty :: Bool
isChatty = False

-- | Used to generate output when chatty
chatty :: String -> IO ()
chatty = when isChatty . putStrLn


-- | Called with a list of paths to test files.  This will remove the
-- file extension from the test file to find a filepath to a binary
-- (executable) corresponding to that test file.  The macaw-arm
-- library will then be used to discover semantics on the binary and
-- these will be compared to the semantics described in the test file.
armAsmTests :: [FilePath] -> T.TestTree
armAsmTests = T.testGroup "ARM" . map mkTest


-- | Read in a test case from disk and output a test tree.
mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp $ do x <- getExpected fp
                               withELF exeFilename $ testDiscovery x
  where
    asmFilename = dropExtension fp
    exeFilename = replaceExtension asmFilename "exe"


-- ----------------------------------------------------------------------
-- Parser/representation for files that contain expected results of
-- semantics discovery from a binary.

newtype Hex a = Hex a
  deriving (Eq, Ord, Num, PrintfArg)

instance (Num a, Show a, PrintfArg a) => Show (Hex a) where
  show (Hex a) = printf "0x%x" a

instance (Read a) => Read (Hex a) where
  readsPrec i s = [ (Hex a, s') | (a, s') <- readsPrec i s ]

-- | The type of expected results for test cases
data ExpectedResultFileData =
  R { funcs :: [(Hex Word64, [(Hex Word64, Word64)])]
    -- ^ The first element of the pair is the address of entry point
    -- of the function.  The list is a list of the addresses of the
    -- basic blocks in the function (including the first block).
    , ignoreBlocks :: [Hex Word64]
    -- ^ This is a list of discovered blocks to ignore.  This is
    -- basically just the address of the instruction after the exit
    -- syscall, as macaw doesn't know that exit never returns and
    -- discovers a false block after exit.
    }
  deriving (Read, Show, Eq)

type ExpectedResult = (M.Map (Hex Word64) (S.Set (Hex Word64, Word64)),
                        S.Set (Hex Word64))

data ExpectedException = BadExpectedFile String
                         deriving (Typeable, Show)

instance Exception ExpectedException


getExpected :: FilePath -> IO ExpectedResult
getExpected expectedFilename = do
  expectedString <- readFile expectedFilename
  case readMaybe expectedString of
    -- Above: Read in the ExpectedResultFileData from the contents of the file
    -- Nothing -> T.assertFailure ("Invalid expected result: " ++ show expectedString)
    Nothing -> throwM $ BadExpectedFile ("Invalid expected spec: " ++ show expectedString)
    Just er ->
      let expectedEntries = M.fromList [ (entry, S.fromList starts) | (entry, starts) <- funcs er ]
          -- expectedEntries maps function entry points to the set of block starts
          -- within the function.
          ignoredBlocks = S.fromList (ignoreBlocks er)
      in return (expectedEntries, ignoredBlocks)


testDiscovery :: ExpectedResult -> E.Elf w -> IO ()
testDiscovery expRes elf =
    case E.elfClass elf of
      E.ELFCLASS32 -> testDiscovery32 expRes elf
      E.ELFCLASS64 -> error "testDiscovery64 TBD"

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery32 :: ExpectedResult -> E.Elf 32 -> IO ()
testDiscovery32 (funcblocks, ignored) elf =
  withMemory MM.Addr32 elf $ \mem -> do
    let Just entryPoint = MM.asSegmentOff mem epinfo
        epinfo = findEntryPoint elf mem
    when isChatty $
         do chatty $ "entryPoint: " <> show entryPoint
            chatty $ "sections = " <> show (ARMELF.getElfSections elf) <> "\n"
            chatty $ "symbols = "
            putDoc $ ARMELF.getELFSymbols elf
            chatty ""

    let discoveryInfo = MD.cfgFromAddrs RO.arm_linux_info mem mempty [entryPoint] []
    chatty $ "di = " <> (show $ MD.ppDiscoveryStateBlocks discoveryInfo) <> "\n"

    let getAbsBlkAddr = fromJust . MM.asAbsoluteAddr . MM.segoffAddr . MD.pblockAddr
        getAbsFunAddr = fromJust . MM.asAbsoluteAddr . MM.segoffAddr . MD.discoveredFunAddr


    let allFoundBlockAddrs :: S.Set Word64
        allFoundBlockAddrs =
            S.fromList [ fromIntegral $ getAbsBlkAddr pbr
                       | PU.Some dfi <- M.elems (discoveryInfo ^. MD.funInfo)
                       , pbr <- M.elems (dfi ^. MD.parsedBlocks)
                       ]

    -- Test that all discovered blocks were expected (and verify their sizes)
    F.forM_ (M.elems (discoveryInfo ^. MD.funInfo)) $ \(PU.Some dfi) ->
        do let actualEntry = fromIntegral $ getAbsFunAddr dfi
               actualBlockStarts = S.fromList [ (baddr, bsize)
                                              | pbr <- M.elems (dfi ^. MD.parsedBlocks)
                                              , let baddr = fromIntegral $ getAbsBlkAddr pbr
                                              , let bsize = fromIntegral (MD.blockSize pbr)
                                              ]
           chatty $ "actualEntry: " <> show actualEntry
           chatty $ "actualBlockStarts: " <> show actualBlockStarts
           case (S.member actualEntry ignored, M.lookup actualEntry funcblocks) of
             (True, _) -> return ()
             (_, Nothing) -> T.assertFailure (printf "Unexpected block start: 0x%x" actualEntry)
             (_, Just expectedBlockStarts) ->
                 T.assertEqual (printf "Block starts for 0x%x" actualEntry)
                                     expectedBlockStarts (actualBlockStarts `removeIgnored` ignored)

    -- Test that all expected blocks were discovered
    F.forM_ funcblocks $ \blockAddrs ->
        F.forM_ blockAddrs $ \(blockAddr@(Hex addr), _) ->
            T.assertBool ("Missing block address: " ++ show blockAddr) (S.member addr allFoundBlockAddrs)

    T.assertBool "everything looks good" True


removeIgnored :: (Ord b, Ord a) => S.Set (a, b) -> S.Set a -> S.Set (a, b)
removeIgnored actualBlockStarts ignoredBlocks =
    let removeIfPresent v@(addr, _) acc = if S.member addr ignoredBlocks
                                          then S.delete v acc
                                          else acc
    in F.foldr removeIfPresent actualBlockStarts actualBlockStarts
