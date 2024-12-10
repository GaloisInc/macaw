{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main (main) where

import           Control.Lens ( (^.) )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ElfEdit as Elf
import qualified Data.Foldable as F
import qualified Data.Map as Map
import           Data.Maybe ( mapMaybe )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeNats ( KnownNat, type (<=) )
import qualified Prettyprinter as PP
import           System.FilePath ( (</>), (<.>) )
import qualified System.FilePath.Glob as SFG
import qualified System.IO as IO
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Testing as MST
import qualified Data.Macaw.RISCV as MR
import qualified Data.Macaw.RISCV.Symbolic as MRS
import qualified Data.Macaw.RISCV.Symbolic.Regs as MRSR
import qualified GRIFT.Types as G
import qualified What4.Config as WC
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.ProblemFeatures as WPF
import qualified What4.Solver as WS

import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.LLVM.MemModel as LLVM

-- | A Tasty option to tell us to save SMT queries and responses to /tmp for debugging purposes
data SaveSMT = SaveSMT Bool
  deriving (Eq, Show)

instance TTO.IsOption SaveSMT where
  defaultValue = SaveSMT False
  parseValue v = SaveSMT <$> TTO.safeReadBool v
  optionName = pure "save-smt"
  optionHelp = pure "Save SMT sessions to files in /tmp for debugging"

-- | A tasty option to have the test suite save the macaw IR for each test case to /tmp for debugging purposes
data SaveMacaw = SaveMacaw Bool

instance TTO.IsOption SaveMacaw where
  defaultValue = SaveMacaw False
  parseValue v = SaveMacaw <$> TTO.safeReadBool v
  optionName = pure "save-macaw"
  optionHelp = pure "Save Macaw IR for each test case to /tmp for debugging"

ingredients :: [TTR.Ingredient]
ingredients = TT.includingOptions [ TTO.Option (Proxy @SaveSMT)
                                  , TTO.Option (Proxy @SaveMacaw)
                                  ] : TT.defaultIngredients

getRegName ::
  Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV G.RV32GC)) t ->
  String
getRegName reg =
  case Ctx.intIndex (Ctx.indexVal reg) (Ctx.size regs) of
    Just (Some i) ->
      let r = regs Ctx.! i
          rName = MS.crucGenArchRegName MRS.riscvMacawSymbolicFns r
      in show rName
    Nothing -> error "impossible"
  where regs = MS.crucGenRegAssignment (MRS.riscvMacawSymbolicFns @G.RV32GC)

main :: IO ()
main = do
  -- These are pass/fail in that the assertions in the "pass" set are true (and
  -- the solver returns Unsat), while the assertions in the "fail" set are false
  -- (and the solver returns Sat).
  passTestFilePaths <- SFG.glob "tests/pass/**/*.exe"
  failTestFilePaths <- SFG.glob "tests/fail/**/*.exe"
  let passRes = MST.SimulationResult MST.Unsat
  let failRes = MST.SimulationResult MST.Sat
  let passTests mmPreset = TT.testGroup "True assertions" (map (mkSymExTest passRes mmPreset) passTestFilePaths)
  let failTests mmPreset = TT.testGroup "False assertions" (map (mkSymExTest failRes mmPreset) failTestFilePaths)
  TT.defaultMainWithIngredients ingredients $
    TT.testGroup "macaw-riscv-symbolic tests"
    [ TT.testGroup "Unit tests"
        [ TTH.testCase "pc" $ getRegName (MRSR.pc @G.RV32GC) TTH.@?= "r!pc"
        , TTH.testCase "ra" $ getRegName (MRSR.ra @G.RV32GC) TTH.@?= "r!ra"
        , TTH.testCase "sp" $ getRegName (MRSR.sp @G.RV32GC) TTH.@?= "r!sp"
        , TTH.testCase "gp" $ getRegName (MRSR.gp @G.RV32GC) TTH.@?= "r!gp"
        , TTH.testCase "tp" $ getRegName (MRSR.tp @G.RV32GC) TTH.@?= "r!tp"
        , TTH.testCase "t0" $ getRegName (MRSR.t0 @G.RV32GC) TTH.@?= "r!t0"
        , TTH.testCase "t1" $ getRegName (MRSR.t1 @G.RV32GC) TTH.@?= "r!t1"
        , TTH.testCase "t2" $ getRegName (MRSR.t2 @G.RV32GC) TTH.@?= "r!t2"
        , TTH.testCase "s0" $ getRegName (MRSR.s0 @G.RV32GC) TTH.@?= "r!s0"
        , TTH.testCase "s1" $ getRegName (MRSR.s1 @G.RV32GC) TTH.@?= "r!s1"
        , TTH.testCase "a0" $ getRegName (MRSR.a0 @G.RV32GC) TTH.@?= "r!a0"
        , TTH.testCase "a1" $ getRegName (MRSR.a1 @G.RV32GC) TTH.@?= "r!a1"
        , TTH.testCase "a2" $ getRegName (MRSR.a2 @G.RV32GC) TTH.@?= "r!a2"
        , TTH.testCase "a3" $ getRegName (MRSR.a3 @G.RV32GC) TTH.@?= "r!a3"
        , TTH.testCase "a4" $ getRegName (MRSR.a4 @G.RV32GC) TTH.@?= "r!a4"
        , TTH.testCase "a5" $ getRegName (MRSR.a5 @G.RV32GC) TTH.@?= "r!a5"
        , TTH.testCase "a6" $ getRegName (MRSR.a6 @G.RV32GC) TTH.@?= "r!a6"
        , TTH.testCase "a7" $ getRegName (MRSR.a7 @G.RV32GC) TTH.@?= "r!a7"
        , TTH.testCase "s2" $ getRegName (MRSR.s2 @G.RV32GC) TTH.@?= "r!s2"
        , TTH.testCase "s3" $ getRegName (MRSR.s3 @G.RV32GC) TTH.@?= "r!s3"
        , TTH.testCase "s4" $ getRegName (MRSR.s4 @G.RV32GC) TTH.@?= "r!s4"
        , TTH.testCase "s5" $ getRegName (MRSR.s5 @G.RV32GC) TTH.@?= "r!s5"
        , TTH.testCase "s6" $ getRegName (MRSR.s6 @G.RV32GC) TTH.@?= "r!s6"
        , TTH.testCase "s7" $ getRegName (MRSR.s7 @G.RV32GC) TTH.@?= "r!s7"
        , TTH.testCase "s8" $ getRegName (MRSR.s8 @G.RV32GC) TTH.@?= "r!s8"
        , TTH.testCase "s9" $ getRegName (MRSR.s9 @G.RV32GC) TTH.@?= "r!s9"
        , TTH.testCase "s10" $ getRegName (MRSR.s10 @G.RV32GC) TTH.@?= "r!s10"
        , TTH.testCase "s11" $ getRegName (MRSR.s11 @G.RV32GC) TTH.@?= "r!s11"
        , TTH.testCase "t3" $ getRegName (MRSR.t3 @G.RV32GC) TTH.@?= "r!t3"
        , TTH.testCase "t4" $ getRegName (MRSR.t4 @G.RV32GC) TTH.@?= "r!t4"
        , TTH.testCase "t5" $ getRegName (MRSR.t5 @G.RV32GC) TTH.@?= "r!t5"
        , TTH.testCase "t6" $ getRegName (MRSR.t6 @G.RV32GC) TTH.@?= "r!t6"
        , TTH.testCase "x1" $ getRegName (MRSR.x1 @G.RV32GC) TTH.@?= "r!ra"
        , TTH.testCase "x2" $ getRegName (MRSR.x2 @G.RV32GC) TTH.@?= "r!sp"
        , TTH.testCase "x3" $ getRegName (MRSR.x3 @G.RV32GC) TTH.@?= "r!gp"
        , TTH.testCase "x4" $ getRegName (MRSR.x4 @G.RV32GC) TTH.@?= "r!tp"
        , TTH.testCase "x5" $ getRegName (MRSR.x5 @G.RV32GC) TTH.@?= "r!t0"
        , TTH.testCase "x6" $ getRegName (MRSR.x6 @G.RV32GC) TTH.@?= "r!t1"
        , TTH.testCase "x7" $ getRegName (MRSR.x7 @G.RV32GC) TTH.@?= "r!t2"
        , TTH.testCase "x8" $ getRegName (MRSR.x8 @G.RV32GC) TTH.@?= "r!s0"
        , TTH.testCase "x9" $ getRegName (MRSR.x9 @G.RV32GC) TTH.@?= "r!s1"
        , TTH.testCase "x10" $ getRegName (MRSR.x10 @G.RV32GC) TTH.@?= "r!a0"
        , TTH.testCase "x11" $ getRegName (MRSR.x11 @G.RV32GC) TTH.@?= "r!a1"
        , TTH.testCase "x12" $ getRegName (MRSR.x12 @G.RV32GC) TTH.@?= "r!a2"
        , TTH.testCase "x13" $ getRegName (MRSR.x13 @G.RV32GC) TTH.@?= "r!a3"
        , TTH.testCase "x14" $ getRegName (MRSR.x14 @G.RV32GC) TTH.@?= "r!a4"
        , TTH.testCase "x15" $ getRegName (MRSR.x15 @G.RV32GC) TTH.@?= "r!a5"
        , TTH.testCase "x16" $ getRegName (MRSR.x16 @G.RV32GC) TTH.@?= "r!a6"
        , TTH.testCase "x17" $ getRegName (MRSR.x17 @G.RV32GC) TTH.@?= "r!a7"
        , TTH.testCase "x18" $ getRegName (MRSR.x18 @G.RV32GC) TTH.@?= "r!s2"
        , TTH.testCase "x19" $ getRegName (MRSR.x19 @G.RV32GC) TTH.@?= "r!s3"
        , TTH.testCase "x20" $ getRegName (MRSR.x20 @G.RV32GC) TTH.@?= "r!s4"
        , TTH.testCase "x21" $ getRegName (MRSR.x21 @G.RV32GC) TTH.@?= "r!s5"
        , TTH.testCase "x22" $ getRegName (MRSR.x22 @G.RV32GC) TTH.@?= "r!s6"
        , TTH.testCase "x23" $ getRegName (MRSR.x23 @G.RV32GC) TTH.@?= "r!s7"
        , TTH.testCase "x24" $ getRegName (MRSR.x24 @G.RV32GC) TTH.@?= "r!s8"
        , TTH.testCase "x25" $ getRegName (MRSR.x25 @G.RV32GC) TTH.@?= "r!s9"
        , TTH.testCase "x26" $ getRegName (MRSR.x26 @G.RV32GC) TTH.@?= "r!s10"
        , TTH.testCase "x27" $ getRegName (MRSR.x27 @G.RV32GC) TTH.@?= "r!s11"
        , TTH.testCase "x28" $ getRegName (MRSR.x28 @G.RV32GC) TTH.@?= "r!t3"
        , TTH.testCase "x29" $ getRegName (MRSR.x29 @G.RV32GC) TTH.@?= "r!t4"
        , TTH.testCase "x30" $ getRegName (MRSR.x30 @G.RV32GC) TTH.@?= "r!t5"
        , TTH.testCase "x31" $ getRegName (MRSR.x31 @G.RV32GC) TTH.@?= "r!t6"
        , TTH.testCase "ft0" $ getRegName (MRSR.ft0 @G.RV32GC) TTH.@?= "r!ft0"
        , TTH.testCase "ft1" $ getRegName (MRSR.ft1 @G.RV32GC) TTH.@?= "r!ft1"
        , TTH.testCase "ft2" $ getRegName (MRSR.ft2 @G.RV32GC) TTH.@?= "r!ft2"
        , TTH.testCase "ft3" $ getRegName (MRSR.ft3 @G.RV32GC) TTH.@?= "r!ft3"
        , TTH.testCase "ft4" $ getRegName (MRSR.ft4 @G.RV32GC) TTH.@?= "r!ft4"
        , TTH.testCase "ft5" $ getRegName (MRSR.ft5 @G.RV32GC) TTH.@?= "r!ft5"
        , TTH.testCase "ft6" $ getRegName (MRSR.ft6 @G.RV32GC) TTH.@?= "r!ft6"
        , TTH.testCase "ft7" $ getRegName (MRSR.ft7 @G.RV32GC) TTH.@?= "r!ft7"
        , TTH.testCase "fs0" $ getRegName (MRSR.fs0 @G.RV32GC) TTH.@?= "r!fs0"
        , TTH.testCase "fs1" $ getRegName (MRSR.fs1 @G.RV32GC) TTH.@?= "r!fs1"
        , TTH.testCase "fa0" $ getRegName (MRSR.fa0 @G.RV32GC) TTH.@?= "r!fa0"
        , TTH.testCase "fa1" $ getRegName (MRSR.fa1 @G.RV32GC) TTH.@?= "r!fa1"
        , TTH.testCase "fa2" $ getRegName (MRSR.fa2 @G.RV32GC) TTH.@?= "r!fa2"
        , TTH.testCase "fa3" $ getRegName (MRSR.fa3 @G.RV32GC) TTH.@?= "r!fa3"
        , TTH.testCase "fa4" $ getRegName (MRSR.fa4 @G.RV32GC) TTH.@?= "r!fa4"
        , TTH.testCase "fa5" $ getRegName (MRSR.fa5 @G.RV32GC) TTH.@?= "r!fa5"
        , TTH.testCase "fa6" $ getRegName (MRSR.fa6 @G.RV32GC) TTH.@?= "r!fa6"
        , TTH.testCase "fa7" $ getRegName (MRSR.fa7 @G.RV32GC) TTH.@?= "r!fa7"
        , TTH.testCase "fs2" $ getRegName (MRSR.fs2 @G.RV32GC) TTH.@?= "r!fs2"
        , TTH.testCase "fs3" $ getRegName (MRSR.fs3 @G.RV32GC) TTH.@?= "r!fs3"
        , TTH.testCase "fs4" $ getRegName (MRSR.fs4 @G.RV32GC) TTH.@?= "r!fs4"
        , TTH.testCase "fs5" $ getRegName (MRSR.fs5 @G.RV32GC) TTH.@?= "r!fs5"
        , TTH.testCase "fs6" $ getRegName (MRSR.fs6 @G.RV32GC) TTH.@?= "r!fs6"
        , TTH.testCase "fs7" $ getRegName (MRSR.fs7 @G.RV32GC) TTH.@?= "r!fs7"
        , TTH.testCase "fs8" $ getRegName (MRSR.fs8 @G.RV32GC) TTH.@?= "r!fs8"
        , TTH.testCase "fs9" $ getRegName (MRSR.fs9 @G.RV32GC) TTH.@?= "r!fs9"
        , TTH.testCase "fs10" $ getRegName (MRSR.fs10 @G.RV32GC) TTH.@?= "r!fs10"
        , TTH.testCase "fs11" $ getRegName (MRSR.fs11 @G.RV32GC) TTH.@?= "r!fs11"
        , TTH.testCase "ft8" $ getRegName (MRSR.ft8 @G.RV32GC) TTH.@?= "r!ft8"
        , TTH.testCase "ft9" $ getRegName (MRSR.ft9 @G.RV32GC) TTH.@?= "r!ft9"
        , TTH.testCase "ft10" $ getRegName (MRSR.ft10 @G.RV32GC) TTH.@?= "r!ft10"
        , TTH.testCase "ft11" $ getRegName (MRSR.ft11 @G.RV32GC) TTH.@?= "r!ft11"
        , TTH.testCase "f0" $ getRegName (MRSR.f0 @G.RV32GC) TTH.@?= "r!ft0"
        , TTH.testCase "f1" $ getRegName (MRSR.f1 @G.RV32GC) TTH.@?= "r!ft1"
        , TTH.testCase "f2" $ getRegName (MRSR.f2 @G.RV32GC) TTH.@?= "r!ft2"
        , TTH.testCase "f3" $ getRegName (MRSR.f3 @G.RV32GC) TTH.@?= "r!ft3"
        , TTH.testCase "f4" $ getRegName (MRSR.f4 @G.RV32GC) TTH.@?= "r!ft4"
        , TTH.testCase "f5" $ getRegName (MRSR.f5 @G.RV32GC) TTH.@?= "r!ft5"
        , TTH.testCase "f6" $ getRegName (MRSR.f6 @G.RV32GC) TTH.@?= "r!ft6"
        , TTH.testCase "f7" $ getRegName (MRSR.f7 @G.RV32GC) TTH.@?= "r!ft7"
        , TTH.testCase "f8" $ getRegName (MRSR.f8 @G.RV32GC) TTH.@?= "r!fs0"
        , TTH.testCase "f9" $ getRegName (MRSR.f9 @G.RV32GC) TTH.@?= "r!fs1"
        , TTH.testCase "f10" $ getRegName (MRSR.f10 @G.RV32GC) TTH.@?= "r!fa0"
        , TTH.testCase "f11" $ getRegName (MRSR.f11 @G.RV32GC) TTH.@?= "r!fa1"
        , TTH.testCase "f12" $ getRegName (MRSR.f12 @G.RV32GC) TTH.@?= "r!fa2"
        , TTH.testCase "f13" $ getRegName (MRSR.f13 @G.RV32GC) TTH.@?= "r!fa3"
        , TTH.testCase "f14" $ getRegName (MRSR.f14 @G.RV32GC) TTH.@?= "r!fa4"
        , TTH.testCase "f15" $ getRegName (MRSR.f15 @G.RV32GC) TTH.@?= "r!fa5"
        , TTH.testCase "f16" $ getRegName (MRSR.f16 @G.RV32GC) TTH.@?= "r!fa6"
        , TTH.testCase "f17" $ getRegName (MRSR.f17 @G.RV32GC) TTH.@?= "r!fa7"
        , TTH.testCase "f18" $ getRegName (MRSR.f18 @G.RV32GC) TTH.@?= "r!fs2"
        , TTH.testCase "f19" $ getRegName (MRSR.f19 @G.RV32GC) TTH.@?= "r!fs3"
        , TTH.testCase "f20" $ getRegName (MRSR.f20 @G.RV32GC) TTH.@?= "r!fs4"
        , TTH.testCase "f21" $ getRegName (MRSR.f21 @G.RV32GC) TTH.@?= "r!fs5"
        , TTH.testCase "f22" $ getRegName (MRSR.f22 @G.RV32GC) TTH.@?= "r!fs6"
        , TTH.testCase "f23" $ getRegName (MRSR.f23 @G.RV32GC) TTH.@?= "r!fs7"
        , TTH.testCase "f24" $ getRegName (MRSR.f24 @G.RV32GC) TTH.@?= "r!fs8"
        , TTH.testCase "f25" $ getRegName (MRSR.f25 @G.RV32GC) TTH.@?= "r!fs9"
        , TTH.testCase "f26" $ getRegName (MRSR.f26 @G.RV32GC) TTH.@?= "r!fs10"
        , TTH.testCase "f27" $ getRegName (MRSR.f27 @G.RV32GC) TTH.@?= "r!fs11"
        , TTH.testCase "f28" $ getRegName (MRSR.f28 @G.RV32GC) TTH.@?= "r!ft8"
        , TTH.testCase "f29" $ getRegName (MRSR.f29 @G.RV32GC) TTH.@?= "r!ft9"
        , TTH.testCase "f30" $ getRegName (MRSR.f30 @G.RV32GC) TTH.@?= "r!ft10"
        , TTH.testCase "f31" $ getRegName (MRSR.f31 @G.RV32GC) TTH.@?= "r!ft11"
        , TTH.testCase "mvendorid" $ getRegName (MRSR.mvendorid @G.RV32GC) TTH.@?= "r!MVendorID"
        , TTH.testCase "marchid" $ getRegName (MRSR.marchid @G.RV32GC) TTH.@?= "r!MArchID"
        , TTH.testCase "mimpid" $ getRegName (MRSR.mimpid @G.RV32GC) TTH.@?= "r!MImpID"
        , TTH.testCase "mhartid" $ getRegName (MRSR.mhartid @G.RV32GC) TTH.@?= "r!MHartID"
        , TTH.testCase "mstatus" $ getRegName (MRSR.mstatus @G.RV32GC) TTH.@?= "r!MStatus"
        , TTH.testCase "misa" $ getRegName (MRSR.misa @G.RV32GC) TTH.@?= "r!MISA"
        , TTH.testCase "medeleg" $ getRegName (MRSR.medeleg @G.RV32GC) TTH.@?= "r!MEDeleg"
        , TTH.testCase "mideleg" $ getRegName (MRSR.mideleg @G.RV32GC) TTH.@?= "r!MIDeleg"
        , TTH.testCase "mie" $ getRegName (MRSR.mie @G.RV32GC) TTH.@?= "r!MIE"
        , TTH.testCase "mtvec" $ getRegName (MRSR.mtvec @G.RV32GC) TTH.@?= "r!MTVec"
        , TTH.testCase "mcounteren" $ getRegName (MRSR.mcounteren @G.RV32GC) TTH.@?= "r!MCounterEn"
        , TTH.testCase "mscratch" $ getRegName (MRSR.mscratch @G.RV32GC) TTH.@?= "r!MScratch"
        , TTH.testCase "mepc" $ getRegName (MRSR.mepc @G.RV32GC) TTH.@?= "r!MEPC"
        , TTH.testCase "mcause" $ getRegName (MRSR.mcause @G.RV32GC) TTH.@?= "r!MCause"
        , TTH.testCase "mtval" $ getRegName (MRSR.mtval @G.RV32GC) TTH.@?= "r!MTVal"
        , TTH.testCase "mip" $ getRegName (MRSR.mip @G.RV32GC) TTH.@?= "r!MIP"
        , TTH.testCase "mcycle" $ getRegName (MRSR.mcycle @G.RV32GC) TTH.@?= "r!MCycle"
        , TTH.testCase "minstret" $ getRegName (MRSR.minstret @G.RV32GC) TTH.@?= "r!MInstRet"
        , TTH.testCase "mcycleh" $ getRegName (MRSR.mcycleh @G.RV32GC) TTH.@?= "r!MCycleh"
        , TTH.testCase "minstreth" $ getRegName (MRSR.minstreth @G.RV32GC) TTH.@?= "r!MInstReth"
        , TTH.testCase "frm" $ getRegName (MRSR.frm @G.RV32GC) TTH.@?= "r!FRm"
        , TTH.testCase "fflags" $ getRegName (MRSR.fflags @G.RV32GC) TTH.@?= "r!FFlags"
        , TTH.testCase "fcsr" $ getRegName (MRSR.fcsr @G.RV32GC) TTH.@?= "r!FCSR"
        , TTH.testCase "priv" $ getRegName (MRSR.priv @G.RV32GC) TTH.@?= "r!priv"
        , TTH.testCase "exc" $ getRegName (MRSR.exc @G.RV32GC) TTH.@?= "r!exc"
        ]
    , TT.testGroup "Binary Tests" $
      map (\mmPreset ->
            TT.testGroup (MST.describeMemModelPreset mmPreset)
                         [passTests mmPreset, failTests mmPreset])
          [MST.DefaultMemModel, MST.LazyMemModel]
    ]

hasTestPrefix :: Some (M.DiscoveryFunInfo arch) -> Maybe (BS8.ByteString, Some (M.DiscoveryFunInfo arch))
hasTestPrefix (Some dfi) = do
  bsname <- M.discoveredFunSymbol dfi
  if BS8.pack "test_" `BS8.isPrefixOf` bsname
    then return (bsname, Some dfi)
    else Nothing

-- | RISC-V functions with a single scalar return value return it in @a0@.
--
-- Since all test functions must return a value to assert as true, this is
-- straightforward to extract.
riscvResultExtractor :: ( arch ~ MR.RISCV rv
                        , CB.IsSymInterface sym
                        , MC.ArchConstraints arch
                        , MS.ArchInfo arch
                        , KnownNat (G.RVWidth rv)
                        )
                     => MS.ArchVals arch
                     -> MST.ResultExtractor sym arch
riscvResultExtractor archVals = MST.ResultExtractor $ \regs _mem k -> do
  let re = MS.lookupReg archVals regs MR.GPR_A0
  k PC.knownRepr (CS.regValue re)

mkSymExTest :: MST.SimulationResult -> MST.MemModelPreset -> FilePath -> TT.TestTree
mkSymExTest expected mmPreset exePath = TT.askOption $ \saveSMT@(SaveSMT _) -> TT.askOption $ \saveMacaw@(SaveMacaw _) -> TTH.testCaseSteps exePath $ \step -> do
  bytes <- BS.readFile exePath
  case Elf.decodeElfHeaderInfo bytes of
    Left (_, msg) -> TTH.assertFailure ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (Elf.SomeElf ehi) -> do
      case Elf.headerClass (Elf.header ehi) of
        Elf.ELFCLASS32 ->
          symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi (MR.riscv_info G.rv32GCRepr)
        Elf.ELFCLASS64 ->
          symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi (MR.riscv_info G.rv64GCRepr)

data MacawRISCVSymbolicData t = MacawRISCVSymbolicData

symExTestSized :: forall rv w arch
                . ( w ~ G.RVWidth rv
                  , 16 <= w
                  , MC.ArchConstraints arch
                  , arch ~ MR.RISCV rv
                  , Elf.ElfWidthConstraints w
                  , KnownNat w
                  , MS.ArchInfo arch
                  )
               => MST.SimulationResult
               -> MST.MemModelPreset
               -> FilePath
               -> SaveSMT
               -> SaveMacaw
               -> (String -> IO ())
               -> Elf.ElfHeaderInfo w
               -> MAI.ArchitectureInfo arch
               -> TTH.Assertion
symExTestSized expected mmPreset exePath saveSMT saveMacaw step ehi archInfo = do
   binfo <- MST.runDiscovery ehi exePath MST.toAddrSymMap archInfo MR.riscvPLTStubInfo
   let funInfos = Map.elems (MST.binaryDiscState (MST.mainBinaryInfo binfo) ^. M.funInfo)
   let testEntryPoints = mapMaybe hasTestPrefix funInfos
   F.forM_ testEntryPoints $ \(name, Some dfi) -> do
     step ("Testing " ++ BS8.unpack name ++ " at " ++ show (M.discoveredFunAddr dfi))
     writeMacawIR saveMacaw (BS8.unpack name) dfi
     Some (gen :: PN.NonceGenerator IO t) <- PN.newIONonceGenerator
     sym <- WEB.newExprBuilder WEB.FloatRealRepr MacawRISCVSymbolicData gen
     CBO.withYicesOnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
       -- We are using the z3 backend to discharge proof obligations, so
       -- we need to add its options to the backend configuration
       let solver = WS.z3Adapter
       let backendConf = WI.getConfiguration sym
       WC.extendConfig (WS.solver_adapter_config_options solver) backendConf

       execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend bak)
       archVals <- case MS.archVals (Proxy @(MR.RISCV rv)) Nothing of
                     Just archVals -> pure archVals
                     Nothing -> error "symExTestSized: impossible"
       let extract = riscvResultExtractor archVals
       logger <- makeGoalLogger saveSMT solver name exePath
       let ?memOpts = LLVM.defaultMemOptions
       simRes <- MST.simulateAndVerify solver logger bak execFeatures archInfo archVals binfo mmPreset extract dfi
       TTH.assertEqual "AssertionResult" expected simRes

writeMacawIR :: (MC.ArchConstraints arch) => SaveMacaw -> String -> M.DiscoveryFunInfo arch ids -> IO ()
writeMacawIR (SaveMacaw sm) name dfi
  | not sm = return ()
  | otherwise = writeFile (toSavedMacawPath name) (show (PP.pretty dfi))

toSavedMacawPath :: String -> FilePath
toSavedMacawPath testName = "/tmp" </> name <.> "macaw"
  where
    name = fmap escapeSlash testName

-- | Construct a solver logger that saves the SMT session for the goal solving
-- in /tmp (if requested by the save-smt option)
--
-- The adapter name is included so that, if the same test is solved with
-- multiple solvers, we can differentiate them.
makeGoalLogger :: SaveSMT -> WS.SolverAdapter st -> BS8.ByteString -> FilePath -> IO WS.LogData
makeGoalLogger (SaveSMT saveSMT) adapter funName p
  | not saveSMT = return WS.defaultLogData
  | otherwise = do
      hdl <- IO.openFile (toSavedSMTSessionPath adapter funName p) IO.WriteMode
      return (WS.defaultLogData { WS.logHandle = Just hdl })


-- | Construct a path in /tmp to save the SMT session to
--
-- Just take the original path name and turn all of the slashes into underscores to escape them
toSavedSMTSessionPath :: WS.SolverAdapter st -> BS8.ByteString -> FilePath -> FilePath
toSavedSMTSessionPath adapter funName p = "/tmp" </> filename <.> "smtlib2"
  where
    filename = concat [ fmap escapeSlash p
                      , "_"
                      , BS8.unpack funName
                      , "_"
                      , WS.solver_adapter_name adapter
                      ]

escapeSlash :: Char -> Char
escapeSlash '/' = '_'
escapeSlash c = c
