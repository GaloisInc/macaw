{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module ARMTests
    ( armAsmTests
    )
    where


import           Control.Monad.Catch (throwM, Exception)
import qualified Data.ElfEdit as E
import qualified Data.Foldable as F
import qualified Data.Macaw.ARM as RO
import qualified Data.Macaw.ARM.BinaryFormat.ELF as ARMELF
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BVType )
import qualified Data.Map as M
import           Data.Monoid
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as S
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import qualified SemMC.ARM as ARM
import           Shared
import           System.FilePath ( dropExtension, replaceExtension )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import           Text.PrettyPrint.ANSI.Leijen ( putDoc )
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

-- import qualified Data.Macaw.PPC.BinaryFormat.ELF as E -- KWQ: replacement should be complete
-- import qualified SemMC.Architecture.PPC64 as PPC64

armAsmTests :: [FilePath] -> T.TestTree
armAsmTests = T.testGroup "ARM" . map mkTest

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


-- | Read in a test case from disk and output a test tree.
mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp $ do x <- getExpected fp
                               withELF exeFilename $ testDiscovery x
  where
    asmFilename = dropExtension fp
    exeFilename = replaceExtension asmFilename "exe"


testDiscovery :: ExpectedResult -> E.Elf w -> IO ()
testDiscovery expres elf =
    case E.elfClass elf of
      E.ELFCLASS32 -> testDiscovery32 expres elf
      E.ELFCLASS64 -> error "testDiscovery64 TBD"

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery32 :: ExpectedResult -> E.Elf 32 -> IO ()
testDiscovery32 (funcblocks, ignored) elf =
  withMemory MM.Addr32 elf $ \mem -> do
    let Just entryPoint = MM.asSegmentOff mem epinfo
        epinfo = findEntryPoint elf mem
    putStrLn $ "entryPoint: " <> show entryPoint

    let mbAddrs :: Either String (M.Map
                                      (MM.MemAddr 32)
                                      (MA.AbsValue 32 (BVType 32)))
        mbAddrs = ARMELF.parseELFInfo (Proxy @ARM.ARM) elf

    putStrLn $ "sections = " <> show mbAddrs <> "\n"
    putStrLn $ "symbols = "
    putDoc $ ARMELF.getELFSymbols elf

    T.assertBool ("sections = " <> show mbAddrs) False
