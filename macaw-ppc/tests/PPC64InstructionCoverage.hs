{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module PPC64InstructionCoverage (
  ppc64InstructionCoverageTests
  )
where

import           Control.Lens ( (^.) )
import           Control.Monad ( when )
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( fromJust )
import qualified Data.Set as S
import           Data.Word ( Word64 )
import qualified System.FilePath as FP
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Data.ElfEdit as E

import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.BinaryLoader as MBL
import           Data.Macaw.BinaryLoader.PPC ()
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Some as PU

import           Shared

ppc64InstructionCoverageTests :: [FilePath] -> T.TestTree
ppc64InstructionCoverageTests = T.testGroup "PPCCoverage" . map mkTest

mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp (withPPCELF fp (testMacaw fp))

testMacaw
  :: (MC.ArchAddrWidth arch ~ w, MC.MemWidth w, MBL.BinaryLoader arch (E.ElfHeaderInfo w))
  => FilePath
  -> MAI.ArchitectureInfo arch
  -> MBL.LoadedBinary arch (E.ElfHeaderInfo w)
  -> IO ()
testMacaw fpath archInfo loadedBinary = do
  entries <- MBL.entryPoints loadedBinary
  let mem = MBL.memoryImage loadedBinary
  let di = MD.cfgFromAddrs archInfo mem M.empty (F.toList entries) []
  let allFoundBlockAddrs :: S.Set Word64
      allFoundBlockAddrs =
        S.fromList [ fromIntegral (fromJust (MM.asAbsoluteAddr (MM.segoffAddr (MD.pblockAddr pbr))))
                   | PU.Some dfi <- M.elems (di ^. MD.funInfo)
                   , pbr <- M.elems (dfi ^. MD.parsedBlocks)
                   ]
  T.assertBool "No blocks found" (not (S.null allFoundBlockAddrs))
  when (FP.takeFileName fpath == "gzip") $
    -- This is pretty specific, and mostly just designed to notify us
    -- when there has been a change
    T.assertEqual "number of found blocks" 37211 (length allFoundBlockAddrs)
