{-# LANGUAGE DataKinds #-}
module PPC64InstructionCoverage (
  ppc64InstructionCoverageTests
  ) where

import           Control.Lens ( (^.) )
import qualified Data.Map as M
import           Data.Maybe ( fromJust )
import qualified Data.Set as S
import           Data.Word ( Word64 )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as T

import qualified Data.ElfEdit as E

import qualified Data.Parameterized.Some as PU
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.PPC as RO

import           Shared

ppc64InstructionCoverageTests :: [FilePath] -> T.TestTree
ppc64InstructionCoverageTests = T.testGroup "PPCCoverage" . map mkTest

mkTest :: FilePath -> T.TestTree
mkTest fp = T.testCase fp (withELF fp testMacaw)

testMacaw :: E.Elf 64 -> IO ()
testMacaw elf =
  withMemory MM.Addr64 elf $ \mem -> do
    let Just entryPoint = MM.asSegmentOff mem (findEntryPoint64 elf mem)
    let di = MD.cfgFromAddrs RO.ppc64_linux_info mem MD.emptySymbolAddrMap [entryPoint] []
    let allFoundBlockAddrs :: S.Set Word64
        allFoundBlockAddrs =
          S.fromList [ fromIntegral (fromJust (MM.asAbsoluteAddr (MM.relativeSegmentAddr (MD.pblockAddr pbr))))
                     | PU.Some dfi <- M.elems (di ^. MD.funInfo)
                     , pbr <- M.elems (dfi ^. MD.parsedBlocks)
                     ]
    T.assertBool "No blocks found" (not (S.null allFoundBlockAddrs))


