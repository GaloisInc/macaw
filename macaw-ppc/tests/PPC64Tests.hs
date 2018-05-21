{-# LANGUAGE ScopedTypeVariables #-}
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
import           Control.Monad ( unless )
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( fromJust )
import qualified Data.Set as S
import           Data.Word ( Word64 )
import           System.FilePath ( dropExtension, replaceExtension )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

import qualified Data.ElfEdit as E

import qualified Data.Parameterized.Some as PU
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.PPC as RO
import qualified SemMC.Architecture.PPC64 as PPC64

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

allDiscoveredBlocks :: MD.DiscoveryState arch -> [PU.Some (MD.ParsedBlock arch)]
allDiscoveredBlocks di =
  [ PU.Some pbr
  | PU.Some dfi <- M.elems (di ^. MD.funInfo)
  , pbr <- M.elems (dfi ^. MD.parsedBlocks)
  ]

blockTerminator :: MD.ParsedBlock arch ids -> MD.ParsedTermStmt arch ids
blockTerminator = MD.stmtsTerm . MD.blockStatementList

isClassifyFailure :: MD.ParsedTermStmt arch ids -> Bool
isClassifyFailure ts =
  case ts of
    MD.ClassifyFailure {} -> True
    _ -> False

isTranslateError :: MD.ParsedTermStmt arch ids -> Bool
isTranslateError ts =
  case ts of
    MD.ParsedTranslateError {} -> True
    _ -> False

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery :: FilePath -> E.Elf 64 -> IO ()
testDiscovery expectedFilename elf = do
  let loadCfg = MM.defaultLoadOptions
                  { MM.loadRegionIndex = Just 0
                  }

  loadedBinary :: MBL.LoadedBinary PPC64.PPC (E.Elf 64)
               <- MBL.loadBinary loadCfg elf
  entries <- MBL.entryPoints loadedBinary
  let cfg = RO.ppc64_linux_info (MBL.archBinaryData loadedBinary)
  let mem = MBL.memoryImage loadedBinary
  let di = MD.cfgFromAddrs cfg mem M.empty (F.toList entries) []
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
                       | PU.Some pbr <- allDiscoveredBlocks di
                       ]
      -- Test that all discovered blocks were expected (and verify their sizes)
      F.forM_ (M.elems (di ^. MD.funInfo)) $ \(PU.Some dfi) -> do
        F.forM_ (allDiscoveredBlocks di) $ \(PU.Some pb) -> do
          let addr = absoluteFromSegOff (MD.pblockAddr pb)
          unless (S.member addr ignoredBlocks) $ do
            let term = blockTerminator pb
            T.assertBool ("Unclassified block at " ++ show (MD.pblockAddr pb)) (not (isClassifyFailure term))
            T.assertBool ("Translate error at " ++ show (MD.pblockAddr pb)) (not (isTranslateError term))
        let actualEntry = absoluteFromSegOff (MD.discoveredFunAddr dfi)
            actualBlockStarts = S.fromList [ (baddr, bsize)
                                           | pbr <- M.elems (dfi ^. MD.parsedBlocks)
--                                             , trace ("Parsed Block: " ++ show pbr) True
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

absoluteFromSegOff :: MM.MemSegmentOff 64 -> Hex Word64
absoluteFromSegOff = fromIntegral . fromJust . MM.asAbsoluteAddr . MM.relativeSegmentAddr

removeIgnored :: (Ord b, Ord a) => S.Set (a, b) -> S.Set a -> S.Set (a, b)
removeIgnored actualBlockStarts ignoredBlocks =
  F.foldr (\v@(addr, _) acc -> if S.member addr ignoredBlocks
                               then S.delete v acc
                               else acc) actualBlockStarts actualBlockStarts

