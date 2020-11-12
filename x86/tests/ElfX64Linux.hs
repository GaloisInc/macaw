{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
module ElfX64Linux (
  elfX64LinuxTests
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( unless, when )
import qualified Control.Monad.Catch as C
import qualified Data.ByteString as B
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe
import qualified Data.Set as S
import           Data.Typeable ( Typeable )
import           Data.Word ( Word64 )
import           Numeric (showHex)
import           System.FilePath
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import           Text.Printf ( printf )
import           Text.Read ( readMaybe )

import qualified Data.ElfEdit as E

import qualified Data.Parameterized.Some as PU
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.X86 as RO

-- |
elfX64LinuxTests :: [FilePath] -> T.TestTree
elfX64LinuxTests = T.testGroup "ELF x64 Linux" . map mkTest

data Addr = Addr Int Word64
  deriving (Read,Eq, Ord)
-- ^ An address is a region index and offset

instance Show Addr where
  showsPrec _ (Addr idx off) = showString "Addr " . shows idx . showString " 0x" . showHex off

-- | The type of expected results for test cases
data ExpectedResult =
  R { funcs :: [(Addr, [(Addr, Integer)])]
    -- ^ The first element of the pair is the address of entry point
    -- of the function.  The list is a list of the addresses of the
    -- basic blocks in the function (including the first block) and the
    -- size of the block
    , ignoreBlocks :: [Addr]
    -- ^ This is a list of discovered blocks to ignore.  This is
    -- basically just the address of the instruction after the exit
    -- syscall, as macaw doesn't know that exit never returns and
    -- discovers a false block after exit.
    }
  deriving (Read, Show, Eq)

-- | Given a path to an expected file, this
mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp $ withELF elfFilename (testDiscovery fp)
  where
    elfFilename = dropExtension fp

toSegOff :: MM.Memory 64 -> Addr -> MM.MemSegmentOff 64
toSegOff mem (Addr idx off) = do
  let addr :: MM.MemAddr 64
      addr = MM.MemAddr idx (fromIntegral off)
  case MM.asSegmentOff mem addr  of
    Just a -> a
    Nothing ->
      let ppSeg seg = "  Segment: " ++ show (MM.segmentOffAddr seg 0)
       in error $ "Could not resolve address : " ++ show addr ++ "\n"
                  ++ unlines (fmap ppSeg (MM.memSegments mem))

toAddr :: MM.MemSegmentOff 64 -> Addr
toAddr segOff = do
  let addr :: MM.MemAddr 64
      addr = MM.segoffAddr segOff
   in Addr (fromIntegral (MM.addrBase addr)) (fromIntegral (MM.addrOffset addr))

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery :: FilePath -> E.ElfHeaderInfo 64 -> IO ()
testDiscovery expectedFilename elf = do
  let opt = MM.defaultLoadOptions
  (warn, mem, mentry, syms) <-
    case MM.resolveElfContents opt elf of
      Left err -> C.throwM (MemoryLoadError err)
      Right r -> pure r
  when (not (null warn)) $ do
    error $ "Warnings while loading Elf " ++ show warn
  let entries = maybeToList mentry ++ fmap MM.memSymbolStart syms
  let addrSymMap :: M.Map (MM.MemSegmentOff 64) B.ByteString
      addrSymMap = M.fromList [ (MM.memSymbolStart sym, MM.memSymbolName sym)
                              | sym <- syms
                              ]
  let di = MD.cfgFromAddrs RO.x86_64_linux_info mem addrSymMap entries []
  expectedString <- readFile expectedFilename
  case readMaybe expectedString of
    Nothing -> T.assertFailure ("Invalid expected result: " ++ show expectedString)
    Just er -> do
      let expectedEntries :: M.Map (MM.MemSegmentOff 64) (S.Set (Addr, Integer))
          expectedEntries = M.fromList
            [ (toSegOff mem entry
              , S.fromList ((\(s,sz) -> (s, sz)) <$> starts)
              )
            | (entry, starts) <- funcs er
            ]
          ignoredBlocks :: S.Set (MM.MemSegmentOff 64)
          ignoredBlocks = S.fromList (toSegOff mem <$> ignoreBlocks er)
      T.assertEqual "Collection of discovered function starting points"
          (M.keysSet expectedEntries `S.difference` ignoredBlocks)
          (M.keysSet (di ^. MD.funInfo))
      F.forM_ (M.elems (di ^. MD.funInfo)) $ \(PU.Some dfi) -> do
        F.forM_ (M.elems (dfi ^. MD.parsedBlocks)) $ \pb -> do
          let addr = MD.pblockAddr pb
          unless (S.member addr ignoredBlocks) $ do
            let term = MD.pblockTermStmt pb
            case term of
              MD.ClassifyFailure _ rsns -> do
                -- Print a reason with subsequent line sindented more.
                let ppRsn [] = []
                    ppRsn (h:r) = ("  " <> h) : fmap (\s -> "    " <> s) r
                T.assertFailure $ "Unclassified block at " ++ show (MD.pblockAddr pb) ++ "\n"
                  ++ unlines (concatMap (ppRsn . lines) rsns)
              MD.ParsedTranslateError _ ->
                T.assertFailure $ "Translate error at " ++ show (MD.pblockAddr pb) ++ " " ++ show term
              _ ->
                pure ()

        let actualEntry = MD.discoveredFunAddr dfi
            -- actualEntry = fromIntegral (MM.addrValue (MD.discoveredFunAddr dfi))
        let actualBlockStarts :: S.Set (Addr, Integer)
            actualBlockStarts = S.fromList [ (toAddr addr, toInteger (MD.blockSize pbr))
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

withELF :: FilePath -> (E.ElfHeaderInfo 64 -> IO ()) -> IO ()
withELF fp k = do
  bytes <- B.readFile fp
  case E.decodeElfHeaderInfo bytes of
    Left (off,msg) ->
      error ("Error parsing ELF header at offset " ++ show off ++ ": " ++ msg)
    Right (E.SomeElf e) ->
      case E.headerClass (E.header e) of
        E.ELFCLASS32 -> error "ELF32 is unsupported in the test suite"
        E.ELFCLASS64 -> k e

data ElfException = MemoryLoadError String
  deriving (Typeable, Show)

instance C.Exception ElfException
