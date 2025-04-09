{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Ryan Scott <rscott@galois.com>

RISC-V registers.

This module is meant to be imported qualified, as it exports many terse names.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Macaw.RISCV.Symbolic.Regs
  ( RISCVSymbolicException(..)
  , riscvRegName
  , riscvRegAssignment
  , riscvRegStructType
  , regIndexMap
  , lookupReg
  , updateReg
  , PC
  , GPR
  , RA, SP, GP, TP, T0, T1, T2, S0, S1, A0, A1, A2, A3, A4, A5, A6, A7, S2, S3
  , S4, S5, S6, S7, S8, S9, S10, S11, T3, T4, T5, T6
  , X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15, X16, X17
  , X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31
  , FPR
  , FT0, FT1, FT2, FT3, FT4, FT5, FT6, FT7, FS0, FS1, FA0, FA1, FA2, FA3
  , FA4, FA5, FA6, FA7, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FT8
  , FT9, FT10, FT11
  , F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16
  , F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31
  , CSR
  , MVendorID, MArchID, MImpID, MHartID, MStatus, MISA, MEDeleg, MIDeleg, MIE
  , MTVec, MCounterEn, MScratch, MEPC, MCause, MTVal, MIP, MCycle, MInstRet
  , MCycleh, MInstReth, FRm, FFlags, FCSR
  , Priv, EXC
  , pc
  , ra, sp, gp, tp, t0, t1, t2, s0, s1, a0, a1, a2, a3, a4, a5, a6, a7, s2, s3
  , s4, s5, s6, s7, s8, s9, s10, s11, t3, t4, t5, t6
  , x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17
  , x18, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28, x29, x30, x31
  , ft0, ft1, ft2, ft3, ft4, ft5, ft6, ft7, fs0, fs1, fa0, fa1, fa2, fa3
  , fa4, fa5, fa6, fa7, fs2, fs3, fs4, fs5, fs6, fs7, fs8, fs9, fs10, fs11, ft8
  , ft9, ft10, ft11
  , f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16
  , f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31
  , mvendorid, marchid, mimpid, mhartid, mstatus, misa, medeleg, mideleg, mie
  , mtvec, mcounteren, mscratch, mepc, mcause, mtval, mip, mcycle, minstret
  , mcycleh, minstreth, frm, fflags, fcsr
  , priv, exc
  ) where

import           Control.Lens ( (%~), (&) )
import qualified Control.Monad.Catch as X
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Typeable ( Typeable )
import           GHC.TypeLits
import qualified GRIFT.Types as G
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified What4.Interface as W4
import qualified What4.Symbol as W4

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.RISCV as MR
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB

import qualified Data.Macaw.RISCV.Symbolic.Repeat as RR

type instance MS.ArchRegContext (MR.RISCV rv) =
          (Ctx.EmptyCtx Ctx.::> MT.BVType (G.RVWidth rv)  -- PC
  Ctx.<+> RR.CtxRepeat 31 (MT.BVType (G.RVWidth rv))      -- GPR regs. We use 31 instead of 32
                                                          -- because we exclude x0, which is
                                                          -- hardwired to the constant 0.
  Ctx.<+> RR.CtxRepeat 32 (MT.BVType (G.RVFloatWidth rv)) -- FPR regs
  Ctx.<+> RR.CtxRepeat 23 (MT.BVType (G.RVWidth rv))      -- CSR regs. Although there is a
                                                          -- theoretical maximum of 4096 of
                                                          -- these registers, `grift` only
                                                          -- supports 23 of them in practice.
  Ctx.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 2               -- PrivLevel
                        Ctx.::> MT.BoolType))             -- EXC

riscvRegName :: MR.RISCVReg rv tp -> W4.SolverSymbol
riscvRegName r = W4.systemSymbol ("r!" ++ show (MC.prettyF r))

-- Note that `repeatAssign` starts indexing from 0, but we want to exclude
-- `GPR 0` (i.e., x0), as this is always hardwired to the constant 0. As such,
-- we offset all of the indexes by one using (+ 1).
gprRegs :: Ctx.Assignment (MR.RISCVReg rv) (RR.CtxRepeat 31 (MT.BVType (G.RVWidth rv)))
gprRegs = RR.repeatAssign (MR.GPR . fromIntegral . (+ 1))

fprRegs :: Ctx.Assignment (MR.RISCVReg rv) (RR.CtxRepeat 32 (MT.BVType (G.RVFloatWidth rv)))
fprRegs = RR.repeatAssign (MR.FPR . fromIntegral)

-- | The RISC-V control/status registers that are directly supported by Macaw.
csrRegs :: Ctx.Assignment (MR.RISCVReg rv) (RR.CtxRepeat 23 (MT.BVType (G.RVWidth rv)))
csrRegs = RR.repeatAssign (MR.CSR . toEnum)

-- | This contains an assignment that stores the register associated with each index in the
-- RISC-V register structure.
riscvRegAssignment :: Ctx.Assignment (MR.RISCVReg rv) (MS.ArchRegContext (MR.RISCV rv))
riscvRegAssignment =
  Ctx.Empty Ctx.:> MR.PC
  Ctx.<++> gprRegs
  Ctx.<++> fprRegs
  Ctx.<++> csrRegs
  Ctx.<++> (Ctx.Empty Ctx.:> MR.PrivLevel Ctx.:> MR.EXC)

riscvRegStructType ::
     forall rv
   . G.KnownRV rv
  => G.RVRepr rv
  -> C.TypeRepr (MSB.ArchRegStruct (MR.RISCV rv))
riscvRegStructType _rv =
  C.StructRepr $ MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr $ riscvRegAssignment @rv

regIndexMap :: forall rv
             . G.KnownRV rv
            => MSB.RegIndexMap (MR.RISCV rv)
regIndexMap = MSB.mkRegIndexMap assgn sz
  where
    assgn = riscvRegAssignment @rv
    sz = Ctx.size $ MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr assgn

lookupReg :: forall rv m f tp
           . (G.KnownRV rv, Typeable rv, X.MonadThrow m)
          => MR.RISCVReg rv tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes (MR.RISCV rv))
          -> m (f (MS.ToCrucibleType tp))
lookupReg r asgn =
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn Ctx.! MSB.crucibleIndex pair)

updateReg :: forall rv m f tp
           . (G.KnownRV rv, Typeable rv, X.MonadThrow m)
          => MR.RISCVReg rv tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes (MR.RISCV rv))
          -> m (Ctx.Assignment f (MS.MacawCrucibleRegTypes (MR.RISCV rv)))
updateReg r upd asgn = do
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn & MapF.ixF (MSB.crucibleIndex pair) %~ upd)

newtype RISCVSymbolicException rv = MissingRegisterInState (Some (MR.RISCVReg rv))
  deriving Show
instance Typeable rv => X.Exception (RISCVSymbolicException rv)

-- The following definitions are tightly coupled to that of ArchRegContext for
-- RISCV. Unit tests in the test suite ensure that they are consistent with
-- riscvRegAssignment (below).

-- | Program counter.
type PC = 0

-- | A general-purpose register. Note that this excludes @x0@, which is
-- hard-wired to the constant @0@.
type GPR n = 1 + n
-- | Return address (AKA 'X1').
type RA = GPR 0
-- | Stack pointer (AKA 'X2').
type SP = GPR 1
-- | Global pointer (AKA 'X3').
type GP = GPR 2
-- | Thread pointer (AKA 'X4').
type TP = GPR 3
-- | Temporary register (AKA 'X5').
type T0 = GPR 4
-- | Temporary register (AKA 'X6').
type T1 = GPR 5
-- | Temporary register (AKA 'X7').
type T2 = GPR 6
-- | Callee-saved register (AKA 'X8').
type S0 = GPR 7
-- | Callee-saved register (AKA 'X9').
type S1 = GPR 8
-- | Argument register (AKA 'X10').
type A0 = GPR 9
-- | Argument register (AKA 'X11').
type A1 = GPR 10
-- | Argument register (AKA 'X12').
type A2 = GPR 11
-- | Argument register (AKA 'X13').
type A3 = GPR 12
-- | Argument register (AKA 'X14').
type A4 = GPR 13
-- | Argument register (AKA 'X15').
type A5 = GPR 14
-- | Argument register (AKA 'X16').
type A6 = GPR 15
-- | Argument register (AKA 'X17').
type A7 = GPR 16
-- | Callee-saved register (AKA 'X18').
type S2 = GPR 17
-- | Callee-saved register (AKA 'X19').
type S3 = GPR 18
-- | Callee-saved register (AKA 'X20').
type S4 = GPR 19
-- | Callee-saved register (AKA 'X21').
type S5 = GPR 20
-- | Callee-saved register (AKA 'X22').
type S6 = GPR 21
-- | Callee-saved register (AKA 'X23').
type S7 = GPR 22
-- | Callee-saved register (AKA 'X24').
type S8 = GPR 23
-- | Callee-saved register (AKA 'X25').
type S9 = GPR 24
-- | Callee-saved register (AKA 'X26').
type S10 = GPR 25
-- | Callee-saved register (AKA 'X27').
type S11 = GPR 26
-- | Temporary register (AKA 'X28').
type T3 = GPR 27
-- | Temporary register (AKA 'X29').
type T4 = GPR 28
-- | Temporary register (AKA 'X30').
type T5 = GPR 29
-- | Temporary register (AKA 'X31').
type T6 = GPR 30
-- | Return address (AKA 'RA').
type X1 = GPR 0
-- | Stack pointer (AKA 'SP').
type X2 = GPR 1
-- | Global pointer (AKA 'GP').
type X3 = GPR 2
-- | Thread pointer (AKA 'TP').
type X4 = GPR 3
-- | Temporary register (AKA 'T0').
type X5 = GPR 4
-- | Temporary register (AKA 'T1').
type X6 = GPR 5
-- | Temporary register (AKA 'T2').
type X7 = GPR 6
-- | Callee-saved register (AKA 'S0').
type X8 = GPR 7
-- | Callee-saved register (AKA 'S1').
type X9 = GPR 8
-- | Argument register (AKA 'A0').
type X10 = GPR 9
-- | Argument register (AKA 'A1').
type X11 = GPR 10
-- | Argument register (AKA 'A2').
type X12 = GPR 11
-- | Argument register (AKA 'A3').
type X13 = GPR 12
-- | Argument register (AKA 'A4').
type X14 = GPR 13
-- | Argument register (AKA 'A5').
type X15 = GPR 14
-- | Argument register (AKA 'A6').
type X16 = GPR 15
-- | Argument register (AKA 'A7').
type X17 = GPR 16
-- | Callee-saved register (AKA 'S2').
type X18 = GPR 17
-- | Callee-saved register (AKA 'S3').
type X19 = GPR 18
-- | Callee-saved register (AKA 'S4').
type X20 = GPR 19
-- | Callee-saved register (AKA 'S5').
type X21 = GPR 20
-- | Callee-saved register (AKA 'S6').
type X22 = GPR 21
-- | Callee-saved register (AKA 'S7').
type X23 = GPR 22
-- | Callee-saved register (AKA 'S8').
type X24 = GPR 23
-- | Callee-saved register (AKA 'S9').
type X25 = GPR 24
-- | Callee-saved register (AKA 'S10').
type X26 = GPR 25
-- | Callee-saved register (AKA 'S11').
type X27 = GPR 26
-- | Temporary register (AKA 'T3').
type X28 = GPR 27
-- | Temporary register (AKA 'T4').
type X29 = GPR 28
-- | Temporary register (AKA 'T5').
type X30 = GPR 29
-- | Temporary register (AKA 'T6').
type X31 = GPR 30

-- | A floating-point register.
type FPR n = 32 + n
-- | Temporary register (AKA 'F0').
type FT0 = FPR 0
-- | Temporary register (AKA 'F1').
type FT1 = FPR 1
-- | Temporary register (AKA 'F2').
type FT2 = FPR 2
-- | Temporary register (AKA 'F3').
type FT3 = FPR 3
-- | Temporary register (AKA 'F4').
type FT4 = FPR 4
-- | Temporary register (AKA 'F5').
type FT5 = FPR 5
-- | Temporary register (AKA 'F6').
type FT6 = FPR 6
-- | Temporary register (AKA 'F7').
type FT7 = FPR 7
-- | Callee-saved register (AKA 'F8').
type FS0 = FPR 8
-- | Callee-saved register (AKA 'F9').
type FS1 = FPR 9
-- | Argument register (AKA 'F10').
type FA0 = FPR 10
-- | Argument register (AKA 'F11').
type FA1 = FPR 11
-- | Argument register (AKA 'F12').
type FA2 = FPR 12
-- | Argument register (AKA 'F13').
type FA3 = FPR 13
-- | Argument register (AKA 'F14').
type FA4 = FPR 14
-- | Argument register (AKA 'F15').
type FA5 = FPR 15
-- | Argument register (AKA 'F16').
type FA6 = FPR 16
-- | Argument register (AKA 'F17').
type FA7 = FPR 17
-- | Callee-saved register (AKA 'F18').
type FS2 = FPR 18
-- | Callee-saved register (AKA 'F19').
type FS3 = FPR 19
-- | Callee-saved register (AKA 'F20').
type FS4 = FPR 20
-- | Callee-saved register (AKA 'F21').
type FS5 = FPR 21
-- | Callee-saved register (AKA 'F22').
type FS6 = FPR 22
-- | Callee-saved register (AKA 'F23').
type FS7 = FPR 23
-- | Callee-saved register (AKA 'F24').
type FS8 = FPR 24
-- | Callee-saved register (AKA 'F25').
type FS9 = FPR 25
-- | Callee-saved register (AKA 'F26').
type FS10 = FPR 26
-- | Callee-saved register (AKA 'F27').
type FS11 = FPR 27
-- | Temporary register (AKA 'F28').
type FT8 = FPR 28
-- | Temporary register (AKA 'F29').
type FT9 = FPR 29
-- | Temporary register (AKA 'F30').
type FT10 = FPR 30
-- | Temporary register (AKA 'F31').
type FT11 = FPR 31
-- | Temporary register (AKA 'FT0').
type F0 = FPR 0
-- | Temporary register (AKA 'FT1').
type F1 = FPR 1
-- | Temporary register (AKA 'FT2').
type F2 = FPR 2
-- | Temporary register (AKA 'FT3').
type F3 = FPR 3
-- | Temporary register (AKA 'FT4').
type F4 = FPR 4
-- | Temporary register (AKA 'FT5').
type F5 = FPR 5
-- | Temporary register (AKA 'FT6').
type F6 = FPR 6
-- | Temporary register (AKA 'FT7').
type F7 = FPR 7
-- | Callee-saved register (AKA 'FS0').
type F8 = FPR 8
-- | Callee-saved register (AKA 'FS1').
type F9 = FPR 9
-- | Argument register (AKA 'FA0').
type F10 = FPR 10
-- | Argument register (AKA 'FA1').
type F11 = FPR 11
-- | Argument register (AKA 'FA2').
type F12 = FPR 12
-- | Argument register (AKA 'FA3').
type F13 = FPR 13
-- | Argument register (AKA 'FA4').
type F14 = FPR 14
-- | Argument register (AKA 'FA5').
type F15 = FPR 15
-- | Argument register (AKA 'FA6').
type F16 = FPR 16
-- | Argument register (AKA 'FA7').
type F17 = FPR 17
-- | Callee-saved register (AKA 'FS2').
type F18 = FPR 18
-- | Callee-saved register (AKA 'FS3').
type F19 = FPR 19
-- | Callee-saved register (AKA 'FS4').
type F20 = FPR 20
-- | Callee-saved register (AKA 'FS5').
type F21 = FPR 21
-- | Callee-saved register (AKA 'FS6').
type F22 = FPR 22
-- | Callee-saved register (AKA 'FS7').
type F23 = FPR 23
-- | Callee-saved register (AKA 'FS8').
type F24 = FPR 24
-- | Callee-saved register (AKA 'FS9').
type F25 = FPR 25
-- | Callee-saved register (AKA 'FS10').
type F26 = FPR 26
-- | Callee-saved register (AKA 'FS11').
type F27 = FPR 27
-- | Temporary register (AKA 'FT8').
type F28 = FPR 28
-- | Temporary register (AKA 'FT9').
type F29 = FPR 29
-- | Temporary register (AKA 'FT10').
type F30 = FPR 30
-- | Temporary register (AKA 'FT11').
type F31 = FPR 31

-- | A control/status register.
type CSR n = 64 + n
type MVendorID = CSR 0
type MArchID = CSR 1
type MImpID = CSR 2
type MHartID = CSR 3
type MStatus = CSR 4
type MISA = CSR 5
type MEDeleg = CSR 6
type MIDeleg = CSR 7
type MIE = CSR 8
type MTVec = CSR 9
type MCounterEn = CSR 10
type MScratch = CSR 11
type MEPC = CSR 12
type MCause = CSR 13
type MTVal = CSR 14
type MIP = CSR 15
type MCycle = CSR 16
type MInstRet = CSR 17
type MCycleh = CSR 18
type MInstReth = CSR 19
type FRm = CSR 20
type FFlags = CSR 21
type FCSR = CSR 22

-- | Current privilege level.
type Priv = 87

-- | Trip this if something bad happens.
type EXC = 88

-- | Program counter.
pc :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
pc = Ctx.natIndex @PC

-- | Return address (AKA 'x1').
ra :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
ra = Ctx.natIndex @RA

-- | Stack pointer (AKA 'x2').
sp :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
sp = Ctx.natIndex @SP

-- | Global pointer (AKA 'x3').
gp :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
gp = Ctx.natIndex @GP

-- | Thread pointer (AKA 'x4').
tp :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
tp = Ctx.natIndex @TP

-- | Temporary register (AKA 'x5').
t0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t0 = Ctx.natIndex @T0

-- | Temporary register (AKA 'x6').
t1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t1 = Ctx.natIndex @T1

-- | Temporary register (AKA 'x7').
t2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t2 = Ctx.natIndex @T2

-- | Callee-saved register (AKA 'x8').
s0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s0 = Ctx.natIndex @S0

-- | Callee-saved register (AKA 'x9').
s1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s1 = Ctx.natIndex @S1

-- | Argument register (AKA 'x10').
a0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a0 = Ctx.natIndex @A0

-- | Argument register (AKA 'x11').
a1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a1 = Ctx.natIndex @A1

-- | Argument register (AKA 'x12').
a2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a2 = Ctx.natIndex @A2

-- | Argument register (AKA 'x13').
a3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a3 = Ctx.natIndex @A3

-- | Argument register (AKA 'x14').
a4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a4 = Ctx.natIndex @A4

-- | Argument register (AKA 'x15').
a5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a5 = Ctx.natIndex @A5

-- | Argument register (AKA 'x16').
a6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a6 = Ctx.natIndex @A6

-- | Argument register (AKA 'x17').
a7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
a7 = Ctx.natIndex @A7

-- | Callee-saved register (AKA 'x18').
s2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s2 = Ctx.natIndex @S2

-- | Callee-saved register (AKA 'x19').
s3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s3 = Ctx.natIndex @S3

-- | Callee-saved register (AKA 'x20').
s4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s4 = Ctx.natIndex @S4

-- | Callee-saved register (AKA 'x21').
s5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s5 = Ctx.natIndex @S5

-- | Callee-saved register (AKA 'x22').
s6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s6 = Ctx.natIndex @S6

-- | Callee-saved register (AKA 'x23').
s7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s7 = Ctx.natIndex @S7

-- | Callee-saved register (AKA 'x24').
s8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s8 = Ctx.natIndex @S8

-- | Callee-saved register (AKA 'x25').
s9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s9 = Ctx.natIndex @S9

-- | Callee-saved register (AKA 'x26').
s10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s10 = Ctx.natIndex @S10

-- | Callee-saved register (AKA 'x27').
s11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
s11 = Ctx.natIndex @S11

-- | Temporary register (AKA 'x28').
t3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t3 = Ctx.natIndex @T3

-- | Temporary register (AKA 'x29').
t4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t4 = Ctx.natIndex @T4

-- | Temporary register (AKA 'x30').
t5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t5 = Ctx.natIndex @T5

-- | Temporary register (AKA 'x31').
t6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
t6 = Ctx.natIndex @T6

-- | Return address (AKA 'ra').
x1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x1 = Ctx.natIndex @X1

-- | Stack pointer (AKA 'sp').
x2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x2 = Ctx.natIndex @X2

-- | Global pointer (AKA 'gp').
x3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x3 = Ctx.natIndex @X3

-- | Thread pointer (AKA 'tp').
x4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x4 = Ctx.natIndex @X4

-- | Temporary register (AKA 't0').
x5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x5 = Ctx.natIndex @X5

-- | Temporary register (AKA 't1').
x6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x6 = Ctx.natIndex @X6

-- | Temporary register (AKA 't2').
x7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x7 = Ctx.natIndex @X7

-- | Callee-saved register (AKA 's0').
x8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x8 = Ctx.natIndex @X8

-- | Callee-saved register (AKA 's1').
x9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x9 = Ctx.natIndex @X9

-- | Argument register (AKA 'a0').
x10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x10 = Ctx.natIndex @X10

-- | Argument register (AKA 'a1').
x11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x11 = Ctx.natIndex @X11

-- | Argument register (AKA 'a2').
x12 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x12 = Ctx.natIndex @X12

-- | Argument register (AKA 'a3').
x13 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x13 = Ctx.natIndex @X13

-- | Argument register (AKA 'a4').
x14 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x14 = Ctx.natIndex @X14

-- | Argument register (AKA 'a5').
x15 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x15 = Ctx.natIndex @X15

-- | Argument register (AKA 'a6').
x16 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x16 = Ctx.natIndex @X16

-- | Argument register (AKA 'a7').
x17 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x17 = Ctx.natIndex @X17

-- | Callee-saved register (AKA 's2').
x18 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x18 = Ctx.natIndex @X18

-- | Callee-saved register (AKA 's3').
x19 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x19 = Ctx.natIndex @X19

-- | Callee-saved register (AKA 's4').
x20 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x20 = Ctx.natIndex @X20

-- | Callee-saved register (AKA 's5').
x21 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x21 = Ctx.natIndex @X21

-- | Callee-saved register (AKA 's6').
x22 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x22 = Ctx.natIndex @X22

-- | Callee-saved register (AKA 's7').
x23 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x23 = Ctx.natIndex @X23

-- | Callee-saved register (AKA 's8').
x24 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x24 = Ctx.natIndex @X24

-- | Callee-saved register (AKA 's9').
x25 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x25 = Ctx.natIndex @X25

-- | Callee-saved register (AKA 's10').
x26 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x26 = Ctx.natIndex @X26

-- | Callee-saved register (AKA 's11').
x27 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x27 = Ctx.natIndex @X27

-- | Temporary register (AKA 't3').
x28 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x28 = Ctx.natIndex @X28

-- | Temporary register (AKA 't4').
x29 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x29 = Ctx.natIndex @X29

-- | Temporary register (AKA 't5').
x30 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x30 = Ctx.natIndex @X30

-- | Temporary register (AKA 't6').
x31 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
x31 = Ctx.natIndex @X31

-- | Temporary register (AKA 'f0').
ft0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft0 = Ctx.natIndex @FT0

-- | Temporary register (AKA 'f1').
ft1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft1 = Ctx.natIndex @FT1

-- | Temporary register (AKA 'f2').
ft2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft2 = Ctx.natIndex @FT2

-- | Temporary register (AKA 'f3').
ft3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft3 = Ctx.natIndex @FT3

-- | Temporary register (AKA 'f4').
ft4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft4 = Ctx.natIndex @FT4

-- | Temporary register (AKA 'f5').
ft5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft5 = Ctx.natIndex @FT5

-- | Temporary register (AKA 'f6').
ft6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft6 = Ctx.natIndex @FT6

-- | Temporary register (AKA 'f7').
ft7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft7 = Ctx.natIndex @FT7

-- | Callee-saved register (AKA 'f8').
fs0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs0 = Ctx.natIndex @FS0

-- | Callee-saved register (AKA 'f9').
fs1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs1 = Ctx.natIndex @FS1

-- | Argument register (AKA 'f10').
fa0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa0 = Ctx.natIndex @FA0

-- | Argument register (AKA 'f11').
fa1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa1 = Ctx.natIndex @FA1

-- | Argument register (AKA 'f12').
fa2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa2 = Ctx.natIndex @FA2

-- | Argument register (AKA 'f13').
fa3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa3 = Ctx.natIndex @FA3

-- | Argument register (AKA 'f14').
fa4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa4 = Ctx.natIndex @FA4

-- | Argument register (AKA 'f15').
fa5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa5 = Ctx.natIndex @FA5

-- | Argument register (AKA 'f16').
fa6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa6 = Ctx.natIndex @FA6

-- | Argument register (AKA 'f17').
fa7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fa7 = Ctx.natIndex @FA7

-- | Callee-saved register (AKA 'f18').
fs2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs2 = Ctx.natIndex @FS2

-- | Callee-saved register (AKA 'f19').
fs3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs3 = Ctx.natIndex @FS3

-- | Callee-saved register (AKA 'f20').
fs4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs4 = Ctx.natIndex @FS4

-- | Callee-saved register (AKA 'f21').
fs5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs5 = Ctx.natIndex @FS5

-- | Callee-saved register (AKA 'f22').
fs6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs6 = Ctx.natIndex @FS6

-- | Callee-saved register (AKA 'f23').
fs7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs7 = Ctx.natIndex @FS7

-- | Callee-saved register (AKA 'f24').
fs8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs8 = Ctx.natIndex @FS8

-- | Callee-saved register (AKA 'f25').
fs9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs9 = Ctx.natIndex @FS9

-- | Callee-saved register (AKA 'f26').
fs10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs10 = Ctx.natIndex @FS10

-- | Callee-saved register (AKA 'f27').
fs11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
fs11 = Ctx.natIndex @FS11

-- | Temporary register (AKA 'f28').
ft8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft8 = Ctx.natIndex @FT8

-- | Temporary register (AKA 'f29').
ft9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft9 = Ctx.natIndex @FT9

-- | Temporary register (AKA 'f30').
ft10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft10 = Ctx.natIndex @FT10

-- | Temporary register (AKA 'f31').
ft11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
ft11 = Ctx.natIndex @FT11

-- | Temporary register (AKA 'ft0').
f0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f0 = Ctx.natIndex @F0

-- | Temporary register (AKA 'ft1').
f1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f1 = Ctx.natIndex @F1

-- | Temporary register (AKA 'ft2').
f2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f2 = Ctx.natIndex @F2

-- | Temporary register (AKA 'ft3').
f3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f3 = Ctx.natIndex @F3

-- | Temporary register (AKA 'ft4').
f4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f4 = Ctx.natIndex @F4

-- | Temporary register (AKA 'ft5').
f5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f5 = Ctx.natIndex @F5

-- | Temporary register (AKA 'ft6').
f6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f6 = Ctx.natIndex @F6

-- | Temporary register (AKA 'ft7').
f7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f7 = Ctx.natIndex @F7

-- | Callee-saved register (AKA 'fs0').
f8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f8 = Ctx.natIndex @F8

-- | Callee-saved register (AKA 'fs1').
f9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f9 = Ctx.natIndex @F9

-- | Argument register (AKA 'fa0').
f10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f10 = Ctx.natIndex @F10

-- | Argument register (AKA 'fa1').
f11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f11 = Ctx.natIndex @F11

-- | Argument register (AKA 'fa2').
f12 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f12 = Ctx.natIndex @F12

-- | Argument register (AKA 'fa3').
f13 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f13 = Ctx.natIndex @F13

-- | Argument register (AKA 'fa4').
f14 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f14 = Ctx.natIndex @F14

-- | Argument register (AKA 'fa5').
f15 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f15 = Ctx.natIndex @F15

-- | Argument register (AKA 'fa6').
f16 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f16 = Ctx.natIndex @F16

-- | Argument register (AKA 'fa7').
f17 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f17 = Ctx.natIndex @F17

-- | Callee-saved register (AKA 'fs2').
f18 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f18 = Ctx.natIndex @F18

-- | Callee-saved register (AKA 'fs3').
f19 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f19 = Ctx.natIndex @F19

-- | Callee-saved register (AKA 'fs4').
f20 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f20 = Ctx.natIndex @F20

-- | Callee-saved register (AKA 'fs5').
f21 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f21 = Ctx.natIndex @F21

-- | Callee-saved register (AKA 'fs6').
f22 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f22 = Ctx.natIndex @F22

-- | Callee-saved register (AKA 'fs7').
f23 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f23 = Ctx.natIndex @F23

-- | Callee-saved register (AKA 'fs8').
f24 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f24 = Ctx.natIndex @F24

-- | Callee-saved register (AKA 'fs9').
f25 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f25 = Ctx.natIndex @F25

-- | Callee-saved register (AKA 'fs10').
f26 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f26 = Ctx.natIndex @F26

-- | Callee-saved register (AKA 'fs11').
f27 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f27 = Ctx.natIndex @F27

-- | Temporary register (AKA 'ft8').
f28 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f28 = Ctx.natIndex @F28

-- | Temporary register (AKA 'ft9').
f29 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f29 = Ctx.natIndex @F29

-- | Temporary register (AKA 'ft10').
f30 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f30 = Ctx.natIndex @F30

-- | Temporary register (AKA 'ft11').
f31 :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVFloatWidth rv))
f31 = Ctx.natIndex @F31

mvendorid :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mvendorid = Ctx.natIndex @MVendorID

marchid :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
marchid = Ctx.natIndex @MArchID

mimpid :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mimpid = Ctx.natIndex @MImpID

mhartid :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mhartid = Ctx.natIndex @MHartID

mstatus :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mstatus = Ctx.natIndex @MStatus

misa :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
misa = Ctx.natIndex @MISA

medeleg :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
medeleg = Ctx.natIndex @MEDeleg

mideleg :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mideleg = Ctx.natIndex @MIDeleg

mie :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mie = Ctx.natIndex @MIE

mtvec :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mtvec = Ctx.natIndex @MTVec

mcounteren :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mcounteren = Ctx.natIndex @MCounterEn

mscratch :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mscratch = Ctx.natIndex @MScratch

mepc :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mepc = Ctx.natIndex @MEPC

mcause :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mcause = Ctx.natIndex @MCause

mtval :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mtval = Ctx.natIndex @MTVal

mip :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mip = Ctx.natIndex @MIP

mcycle :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mcycle = Ctx.natIndex @MCycle

minstret :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
minstret = Ctx.natIndex @MInstRet

mcycleh :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
mcycleh = Ctx.natIndex @MCycleh

minstreth :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
minstreth = Ctx.natIndex @MInstReth

frm :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
frm = Ctx.natIndex @FRm

fflags :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
fflags = Ctx.natIndex @FFlags

fcsr :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType (G.RVWidth rv))
fcsr = Ctx.natIndex @FCSR

-- | Current privilege level.
priv :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) (MM.LLVMPointerType 2)
priv = Ctx.natIndex @Priv

-- | Trip this if something bad happens.
exc :: Ctx.Index (MS.MacawCrucibleRegTypes (MR.RISCV rv)) C.BoolType
exc = Ctx.natIndex @EXC
