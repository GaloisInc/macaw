{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
module ElfX64Linux (
  elfX64LinuxTests
  ) where

import Control.Lens ( (^.) )
import qualified Control.Monad.Catch as C
import qualified Data.ByteString as B
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Typeable ( Typeable )
import Data.Word ( Word64 )
import System.FilePath ( dropExtension, replaceExtension )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import Text.Printf ( printf )
import Text.Read ( readMaybe )
import Numeric (showHex)

import qualified Data.ElfEdit as E

import qualified Data.Parameterized.Some as PU
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.X86 as RO

elfX64LinuxTests :: [FilePath] -> T.TestTree
elfX64LinuxTests = T.testGroup "ELF x64 Linux" . map mkTest

-- | The type of expected results for test cases
data ExpectedResult =
  R { funcs :: [(Word64, [(Word64, Integer)])]
    -- ^ The first element of the pair is the address of entry point
    -- of the function.  The list is a list of the addresses of the
    -- basic blocks in the function (including the first block).
    , ignoreBlocks :: [Word64]
    -- ^ This is a list of discovered blocks to ignore.  This is
    -- basically just the address of the instruction after the exit
    -- syscall, as macaw doesn't know that exit never returns and
    -- discovers a false block after exit.
    }
  deriving (Read, Show, Eq)

mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp $ withELF exeFilename (testDiscovery fp)
  where
    asmFilename = dropExtension fp
    exeFilename = replaceExtension asmFilename "exe"

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery :: FilePath -> E.Elf 64 -> IO ()
testDiscovery expectedFilename elf =
  withMemory MM.Addr64 elf $ \mem mentry -> do
    let Just entryPoint = mentry
        di = MD.cfgFromAddrs RO.x86_64_linux_info mem M.empty [entryPoint] []
    let memIdx = case E.elfType elf of
                   E.ET_DYN -> 1
                   E.ET_EXEC -> 0
                   eidx -> error $ "Unexpected elf type " ++ show eidx
    expectedString <- readFile expectedFilename
    case readMaybe expectedString of
      Nothing -> T.assertFailure ("Invalid expected result: " ++ show expectedString)
      Just er -> do
        let toSegOff :: Word64 -> MM.MemSegmentOff 64
            toSegOff off =
                case MM.resolveAddr mem memIdx (fromIntegral off) of
                  Just a -> a
                  Nothing -> error $ "Could not resolve offset " ++ showHex off ""
        let expectedEntries = M.fromList
              [ (toSegOff entry
                , S.fromList ((\(s,sz) -> (toSegOff s, sz)) <$> starts)
                )
                | (entry, starts) <- funcs er
                ]
            ignoredBlocks :: S.Set (MM.MemSegmentOff 64)
            ignoredBlocks = S.fromList (toSegOff <$> ignoreBlocks er)
        T.assertEqual "Collection of discovered function starting points"
          (M.keysSet expectedEntries `S.difference` ignoredBlocks)
          (M.keysSet (di ^. MD.funInfo))
        F.forM_ (M.elems (di ^. MD.funInfo)) $ \(PU.Some dfi) -> do
          let actualEntry = MD.discoveredFunAddr dfi
              -- actualEntry = fromIntegral (MM.addrValue (MD.discoveredFunAddr dfi))
              actualBlockStarts = S.fromList [ (addr, toInteger (MD.blockSize pbr))
                                             | pbr <- M.elems (dfi ^. MD.parsedBlocks)
                                             , let addr = MD.pblockAddr pbr
                                             , addr `S.notMember` ignoredBlocks
                                             ]
          case (S.member actualEntry ignoredBlocks, M.lookup actualEntry expectedEntries) of
            (True, _) -> return ()
            (_, Nothing) ->
              T.assertFailure (printf "Unexpected entry point: %s" (show actualEntry))
            (_, Just expectedBlockStarts) ->
              T.assertEqual (printf "Block starts for %s" (show actualEntry))
                expectedBlockStarts
                actualBlockStarts

withELF :: FilePath -> (E.Elf 64 -> IO ()) -> IO ()
withELF fp k = do
  bytes <- B.readFile fp
  case E.parseElf bytes of
    E.ElfHeaderError off msg ->
      error ("Error parsing ELF header at offset " ++ show off ++ ": " ++ msg)
    E.Elf32Res [] _e32 -> error "ELF32 is unsupported in the test suite"
    E.Elf64Res [] e64 -> k e64
    E.Elf32Res errs _ -> error ("Errors while parsing ELF file: " ++ show errs)
    E.Elf64Res errs _ -> error ("Errors while parsing ELF file: " ++ show errs)

withMemory :: forall w m a
            . (C.MonadThrow m, MM.MemWidth w, Integral (E.ElfWordType w))
           => MM.AddrWidthRepr w
           -> E.Elf w
           -> (MM.Memory w -> Maybe (MM.MemSegmentOff w) -> m a)
           -> m a
withMemory _relaWidth e k = do
  let opt = MM.LoadOptions { MM.loadRegionIndex = Nothing
                           , MM.loadRegionBaseOffset = 0
                           }
  case MM.resolveElfContents opt e of
    Left err -> C.throwM (MemoryLoadError err)
    Right (warn, mem, mentry, _sym) ->
      if length warn >= 3 then
        k mem mentry
       else
        error $ "Warnings while loading Elf " ++ show warn

data ElfException = MemoryLoadError String
  deriving (Typeable, Show)

instance C.Exception ElfException
