{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
module PPC64InstructionCoverage (
  ppc64InstructionCoverageTests
  ) where

import           Control.Lens ( (^.) )
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( fromJust )
import qualified Data.Set as S
import           Data.Word ( Word64 )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Data.ElfEdit as E

import qualified Data.Macaw.BinaryLoader as MBL
import           Data.Macaw.BinaryLoader.PPC ()
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MM
import qualified Data.Macaw.PPC as RO
import qualified Data.Parameterized.Some as PU
import qualified SemMC.Architecture.PPC64 as PPC64

import           Shared

ppc64InstructionCoverageTests :: [FilePath] -> T.TestTree
ppc64InstructionCoverageTests = T.testGroup "PPCCoverage" . map mkTest

mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp (withELF fp testMacaw)

testMacaw :: E.Elf 64 -> IO ()
testMacaw elf = do
  let loadCfg = MM.defaultLoadOptions { MM.loadRegionIndex = Just 0 }
  loadedBinary :: MBL.LoadedBinary PPC64.PPC (E.Elf 64)
               <- MBL.loadBinary loadCfg elf
  entries <- MBL.entryPoints loadedBinary
  let cfg = RO.ppc64_linux_info loadedBinary
  let mem = MBL.memoryImage loadedBinary
  let di = MD.cfgFromAddrs cfg mem M.empty (F.toList entries) []
  let allFoundBlockAddrs :: S.Set Word64
      allFoundBlockAddrs =
        S.fromList [ fromIntegral (fromJust (MM.asAbsoluteAddr (MM.relativeSegmentAddr (MD.pblockAddr pbr))))
                   | PU.Some dfi <- M.elems (di ^. MD.funInfo)
                   , pbr <- M.elems (dfi ^. MD.parsedBlocks)
                   ]
  T.assertBool "No blocks found" (not (S.null allFoundBlockAddrs))


