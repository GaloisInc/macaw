{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module PPCTests (
    SaveMacaw(..)
  , ppcAsmTests
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( unless )
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( fromJust )
import qualified Data.Set as S
import           Data.Word ( Word64 )
import qualified Prettyprinter as PP
import           System.FilePath ( dropExtension, replaceExtension, takeFileName, (<.>), (</>) )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T
import qualified Test.Tasty.Options as TTO
import           Text.Printf ( PrintfArg, printf )
import           Text.Read ( readMaybe )

import qualified Data.ElfEdit as E

import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.BinaryLoader.PPC ()
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Some as PU

import           Shared

data SaveMacaw = SaveMacaw Bool

instance TTO.IsOption SaveMacaw where
  defaultValue = SaveMacaw False
  parseValue v = SaveMacaw <$> TTO.safeReadBool v
  optionName = pure "save-macaw"
  optionHelp = pure "Save Macaw IR for each test case to /tmp for debugging"

ppcAsmTests :: String -> [FilePath] -> T.TestTree
ppcAsmTests groupName = T.testGroup groupName . map mkTest

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
mkTest fp = T.askOption $ \saveMacaw@(SaveMacaw _) -> T.testCase fp $ withPPCELF exeFilename (testDiscovery saveMacaw fp)
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
blockTerminator = MD.pblockTermStmt

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

escapeSlash :: Char -> Char
escapeSlash '/' = '_'
escapeSlash c = c

toSavedMacawPath :: String -> FilePath
toSavedMacawPath testName = "/tmp" </> name <.> "macaw"
  where
    name = fmap escapeSlash testName

writeMacawIR :: (MC.ArchConstraints arch) => SaveMacaw -> String -> MD.DiscoveryFunInfo arch ids -> IO ()
writeMacawIR (SaveMacaw sm) name dfi
  | not sm = return ()
  | otherwise = writeFile (toSavedMacawPath name) (show (PP.pretty dfi))

-- | Run a test over a given expected result filename and the ELF file
-- associated with it
testDiscovery
  :: (MC.ArchAddrWidth arch ~ w, MBL.BinaryLoader arch (E.ElfHeaderInfo w), MM.MemWidth w, MC.ArchConstraints arch, Show (MC.ArchBlockPrecond arch))
  => SaveMacaw
  -> FilePath
  -> MAI.ArchitectureInfo arch
  -> MBL.LoadedBinary arch (E.ElfHeaderInfo w)
  -> IO ()
testDiscovery saveMacaw expectedFilename archInfo loadedBinary = do
  let testName = takeFileName expectedFilename


  entries <- MBL.entryPoints loadedBinary
  let mem = MBL.memoryImage loadedBinary
  let di = MD.cfgFromAddrs archInfo mem M.empty (F.toList entries) []

  F.forM_ (di ^. MD.funInfo) $ \(PU.Some dfi) -> do
    let funcFileName = testName <.> BSC.unpack (MD.discoveredFunName dfi)
    writeMacawIR saveMacaw funcFileName dfi

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
            S.fromList [ fromIntegral (fromJust (MM.asAbsoluteAddr (MM.segoffAddr (MD.pblockAddr pbr))))
                       | PU.Some pbr <- allDiscoveredBlocks di
                       ]
      -- Test that all discovered blocks were expected (and verify their sizes)
      F.forM_ (M.elems (di ^. MD.funInfo)) $ \(PU.Some dfi) -> do
        F.forM_ (allDiscoveredBlocks di) $ \(PU.Some pb) -> do
          let addr = absoluteFromSegOff (MD.pblockAddr pb)
          unless (S.member addr ignoredBlocks) $ do
            let term = blockTerminator pb
            T.assertBool ("Unclassified block at " ++ show (MD.pblockAddr pb)) (not (isClassifyFailure term))
            T.assertBool ("Translate error at " ++ show (MD.pblockAddr pb) ++ "\n" ++ show term) (not (isTranslateError term))
        let actualEntry = absoluteFromSegOff (MD.discoveredFunAddr dfi)
            actualBlockStarts = S.fromList [ (baddr, bsize)
                                           | pbr <- M.elems (dfi ^. MD.parsedBlocks)
--                                             , trace ("Parsed Block: " ++ show pbr) True
                                           , let baddr = fromIntegral (fromJust (MM.asAbsoluteAddr (MM.segoffAddr (MD.pblockAddr pbr))))
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

absoluteFromSegOff :: (MM.MemWidth w) => MM.MemSegmentOff w -> Hex Word64
absoluteFromSegOff = fromIntegral . fromJust . MM.asAbsoluteAddr . MM.segoffAddr

removeIgnored :: (Ord b, Ord a) => S.Set (a, b) -> S.Set a -> S.Set (a, b)
removeIgnored actualBlockStarts ignoredBlocks =
  F.foldr (\v@(addr, _) acc -> if S.member addr ignoredBlocks
                               then S.delete v acc
                               else acc) actualBlockStarts actualBlockStarts

