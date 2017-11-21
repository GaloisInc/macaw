{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
module PPC64Tests (
  ppcAsmTests
  ) where

import           Control.Lens ( (^.) )
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( fromJust, mapMaybe )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as S
import           Data.Word ( Word64 )
import           System.FilePath ( dropExtension, replaceExtension )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

import qualified Data.ElfEdit as E

import qualified Data.Parameterized.Some as PU
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MD
import qualified Data.Macaw.PPC as RO
import qualified Data.Macaw.PPC.BinaryFormat.ELF as E
import qualified SemMC.Architecture.PPC64 as PPC64

import           Data.List (intercalate)
import           Debug.Trace (trace)

import           Shared

ppcAsmTests :: [FilePath] -> T.TestTree
ppcAsmTests = T.testGroup "PPC" . map mkTest

newtype Hex a = Hex a
  deriving (Eq, Ord, Num, PrintfArg)

instance (Num a, Show a, PrintfArg a) => Show (Hex a) where
  show (Hex a) = printf "0x%x" a

instance (Read a) => Read (Hex a) where
  readsPrec i s = [ (Hex a, s') | (a, s') <- readsPrec i s ]

-- | The type of expected results for test cases
data ExpectedResult =
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

-- | Read in a test case from disk and output a test tree.
mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp $ withELF exeFilename (testDiscovery fp)
  where
    asmFilename = dropExtension fp
    exeFilename = replaceExtension asmFilename "exe"

showSegments :: (MM.MemWidth w) => MM.Memory w -> String
showSegments mem = intercalate "\n" $ map show (MM.memSegments mem)

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery :: FilePath -> E.Elf 64 -> IO ()
testDiscovery expectedFilename elf =
  withMemory MM.Addr64 elf $ \mem -> do
    let Just entryPoint =  trace (showSegments mem) $ MM.asSegmentOff mem (findEntryPoint64 elf mem)
        tocBase = RO.tocBaseForELF (Proxy @PPC64.PPC) elf
        otherEntryAddrs :: [MM.MemAddr 64]
        otherEntryAddrs = E.tocEntryAddrsForElf (Proxy @PPC64.PPC) elf
        otherEntries = mapMaybe (MM.asSegmentOff mem) otherEntryAddrs
        di = MD.cfgFromAddrs (RO.ppc64_linux_info tocBase) mem MD.emptySymbolAddrMap (entryPoint:otherEntries) []
    expectedString <- readFile expectedFilename
    case readMaybe expectedString of
      -- Above: Read in the ExpectedResult from the contents of the file
      Nothing -> T.assertFailure ("Invalid expected result: " ++ show expectedString)
      Just er -> do
        let expectedEntries = M.fromList [ (entry, S.fromList starts) | (entry, starts) <- funcs er ]
            -- expectedEntries maps function entry points to the set of block starts
            -- within the function.
            ignoredBlocks = S.fromList (ignoreBlocks er)
            allFoundBlockAddrs :: S.Set Word64
            allFoundBlockAddrs =
              S.fromList [ fromIntegral (fromJust (MM.asAbsoluteAddr (MM.relativeSegmentAddr (MD.pblockAddr pbr))))
                         | PU.Some dfi <- M.elems (di ^. MD.funInfo)
                         , pbr <- M.elems (dfi ^. MD.parsedBlocks)
                         ]
        -- Test that all discovered blocks were expected (and verify their sizes)
        F.forM_ (M.elems (di ^. MD.funInfo)) $ \(PU.Some dfi) -> do
          let actualEntry = fromIntegral (fromJust (MM.asAbsoluteAddr (MM.relativeSegmentAddr (MD.discoveredFunAddr dfi))))
              actualBlockStarts = S.fromList [ (baddr, bsize)
                                             | pbr <- M.elems (dfi ^. MD.parsedBlocks)
                                             , trace ("Parsed Block: " ++ show pbr) True
                                             , let baddr = fromIntegral (fromJust (MM.asAbsoluteAddr (MM.relativeSegmentAddr (MD.pblockAddr pbr))))
                                             , let bsize = fromIntegral (MD.blockSize pbr)
                                             ]
          case (S.member actualEntry ignoredBlocks, M.lookup actualEntry expectedEntries) of
            (True, _) -> return ()
            (_, Nothing) -> T.assertFailure (printf "Unexpected block start: 0x%x" actualEntry)
            (_, Just expectedBlockStarts) ->
              T.assertEqual (printf "Block starts for 0x%x" actualEntry) expectedBlockStarts (actualBlockStarts `removeIgnored` ignoredBlocks)

        -- Test that all expected blocks were discovered
        F.forM_ (funcs er) $ \(_funcAddr, blockAddrs) ->
          F.forM_ blockAddrs $ \(blockAddr@(Hex addr), _) -> do
          T.assertBool ("Missing block address: " ++ show blockAddr) (S.member addr allFoundBlockAddrs)

removeIgnored :: (Ord b, Ord a) => S.Set (a, b) -> S.Set a -> S.Set (a, b)
removeIgnored actualBlockStarts ignoredBlocks =
  F.foldr (\v@(addr, _) acc -> if S.member addr ignoredBlocks
                               then S.delete v acc
                               else acc) actualBlockStarts actualBlockStarts

