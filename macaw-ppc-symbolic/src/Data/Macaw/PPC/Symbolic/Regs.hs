{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

PPC registers.

This module is meant to be imported qualified, as it exports many terse names.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Macaw.PPC.Symbolic.Regs
  ( RegContext
  , PPCSymbolicException(..)
  , ppcRegName
  , ppcRegAssignment
  , ppcRegStructType
  , getReg
  , regIndexMap
  , lookupReg
  , updateReg
  , IP, LNK, CTR, XER, CR, FPSCR, VSCR, GP, FR
  , R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14, R15, R16
  , R17, R18, R19, R20, R21, R22, R23, R24, R25, R26, R27, R28, R29, R30, R31
  , F0, F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12, F13, F14, F15, F16
  , F17, F18, F19, F20, F21, F22, F23, F24, F25, F26, F27, F28, F29, F30, F31
  , ip, lnk, ctr, xer, cr, fpscr, vscr
  , r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16
  , r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31
  , f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16
  , f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31
  ) where

import           Control.Lens ( (^.), (%~), (&) )
import qualified Control.Monad.Catch as X
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Typeable ( Typeable )
import qualified Dismantle.PPC as D
import           GHC.TypeLits
import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified Lang.Crucible.Types as C
import qualified What4.Interface as C
import qualified What4.Symbol as C

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB
import qualified Data.Macaw.PPC as MP

import qualified Data.Macaw.PPC.Symbolic.Repeat as R

type RegSize v = MC.RegAddrWidth (MP.PPCReg v)
type RegContext v
  =     (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- IP
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- LNK
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- CTR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- XER
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- CR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- FPSCR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- VSCR
  C.<+> R.CtxRepeat 32 (MT.BVType (RegSize v))       -- GPRs
  C.<+> R.CtxRepeat 64 (MT.BVType 128)               -- VSRs

type instance MS.ArchRegContext (MP.AnyPPC v) = RegContext v

ppcRegAssignment :: forall v
                  . ( MP.KnownVariant v )
                 => Ctx.Assignment (MP.PPCReg v) (RegContext v)
ppcRegAssignment =
  (Ctx.Empty Ctx.:> MP.PPC_IP
            Ctx.:> MP.PPC_LNK
            Ctx.:> MP.PPC_CTR
            Ctx.:> MP.PPC_XER
            Ctx.:> MP.PPC_CR
            Ctx.:> MP.PPC_FPSCR
            Ctx.:> MP.PPC_VSCR)
  Ctx.<++> (R.repeatAssign (MP.PPC_GP . D.GPR . fromIntegral) :: Ctx.Assignment (MP.PPCReg v) (R.CtxRepeat 32 (MT.BVType (RegSize v))))
  Ctx.<++> (R.repeatAssign (MP.PPC_FR . D.VSReg . fromIntegral) :: Ctx.Assignment (MP.PPCReg v) (R.CtxRepeat 64 (MT.BVType 128)))

type RegAssign ppc f = Ctx.Assignment f (MS.ArchRegContext ppc)

type IP = 0
type LNK = 1
type CTR = 2
type XER = 3
type CR = 4
type FPSCR = 5
type VSCR = 6
type GP n = 7 + n
type R0 = GP 0
type R1 = GP 1
type R2 = GP 2
type R3 = GP 3
type R4 = GP 4
type R5 = GP 5
type R6 = GP 6
type R7 = GP 7
type R8 = GP 8
type R9 = GP 9
type R10 = GP 10
type R11 = GP 11
type R12 = GP 12
type R13 = GP 13
type R14 = GP 14
type R15 = GP 15
type R16 = GP 16
type R17 = GP 17
type R18 = GP 18
type R19 = GP 19
type R20 = GP 20
type R21 = GP 21
type R22 = GP 22
type R23 = GP 23
type R24 = GP 24
type R25 = GP 25
type R26 = GP 26
type R27 = GP 27
type R28 = GP 28
type R29 = GP 29
type R30 = GP 30
type R31 = GP 31
type FR n = 39 + n
type F0 = FR 0
type F1 = FR 1
type F2 = FR 2
type F3 = FR 3
type F4 = FR 4
type F5 = FR 5
type F6 = FR 6
type F7 = FR 7
type F8 = FR 8
type F9 = FR 9
type F10 = FR 10
type F11 = FR 11
type F12 = FR 12
type F13 = FR 13
type F14 = FR 14
type F15 = FR 15
type F16 = FR 16
type F17 = FR 17
type F18 = FR 18
type F19 = FR 19
type F20 = FR 20
type F21 = FR 21
type F22 = FR 22
type F23 = FR 23
type F24 = FR 24
type F25 = FR 25
type F26 = FR 26
type F27 = FR 27
type F28 = FR 28
type F29 = FR 29
type F30 = FR 30
type F31 = FR 31

-- | Instruction pointer
ip :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
ip = Ctx.natIndex @IP

-- | Link register
lnk :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
lnk = Ctx.natIndex @LNK

-- | Loop count register
ctr :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
ctr = Ctx.natIndex @CTR

-- | Fixed-point exception register
xer :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
xer = Ctx.natIndex @XER

-- | Condition register
cr :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 32)
cr = Ctx.natIndex @CR

-- | Floating-point status and control register
fpscr :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 32)
fpscr = Ctx.natIndex @FPSCR

vscr :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 32)
vscr = Ctx.natIndex @VSCR

r0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r0 = Ctx.natIndex @R0

r1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r1 = Ctx.natIndex @R1

r2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r2 = Ctx.natIndex @R2

r3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r3 = Ctx.natIndex @R3

r4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r4 = Ctx.natIndex @R4

r5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r5 = Ctx.natIndex @R5

r6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r6 = Ctx.natIndex @R6

r7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r7 = Ctx.natIndex @R7

r8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r8 = Ctx.natIndex @R8

r9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r9 = Ctx.natIndex @R9

r10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r10 = Ctx.natIndex @R10

r11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r11 = Ctx.natIndex @R11

r12 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r12 = Ctx.natIndex @R12

r13 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r13 = Ctx.natIndex @R13

r14 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r14 = Ctx.natIndex @R14

r15 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r15 = Ctx.natIndex @R15

r16 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r16 = Ctx.natIndex @R16

r17 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r17 = Ctx.natIndex @R17

r18 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r18 = Ctx.natIndex @R18

r19 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r19 = Ctx.natIndex @R19

r20 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r20 = Ctx.natIndex @R20

r21 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r21 = Ctx.natIndex @R21

r22 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r22 = Ctx.natIndex @R22

r23 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r23 = Ctx.natIndex @R23

r24 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r24 = Ctx.natIndex @R24

r25 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r25 = Ctx.natIndex @R25

r26 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r26 = Ctx.natIndex @R26

r27 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r27 = Ctx.natIndex @R27

r28 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r28 = Ctx.natIndex @R28

r29 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r29 = Ctx.natIndex @R29

r30 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r30 = Ctx.natIndex @R30

r31 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
r31 = Ctx.natIndex @R31

f0 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f0 = Ctx.natIndex @F0

f1 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f1 = Ctx.natIndex @F1

f2 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f2 = Ctx.natIndex @F2

f3 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f3 = Ctx.natIndex @F3

f4 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f4 = Ctx.natIndex @F4

f5 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f5 = Ctx.natIndex @F5

f6 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f6 = Ctx.natIndex @F6

f7 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f7 = Ctx.natIndex @F7

f8 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f8 = Ctx.natIndex @F8

f9 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f9 = Ctx.natIndex @F9

f10 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f10 = Ctx.natIndex @F10

f11 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f11 = Ctx.natIndex @F11

f12 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f12 = Ctx.natIndex @F12

f13 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f13 = Ctx.natIndex @F13

f14 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f14 = Ctx.natIndex @F14

f15 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f15 = Ctx.natIndex @F15

f16 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f16 = Ctx.natIndex @F16

f17 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f17 = Ctx.natIndex @F17

f18 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f18 = Ctx.natIndex @F18

f19 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f19 = Ctx.natIndex @F19

f20 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f20 = Ctx.natIndex @F20

f21 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f21 = Ctx.natIndex @F21

f22 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f22 = Ctx.natIndex @F22

f23 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f23 = Ctx.natIndex @F23

f24 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f24 = Ctx.natIndex @F24

f25 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f25 = Ctx.natIndex @F25

f26 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f26 = Ctx.natIndex @F26

f27 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f27 = Ctx.natIndex @F27

f28 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f28 = Ctx.natIndex @F28

f29 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f29 = Ctx.natIndex @F29

f30 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f30 = Ctx.natIndex @F30

f31 :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType 128)
f31 = Ctx.natIndex @F31

getReg :: forall n t f ppc . (Ctx.Idx n (MS.ArchRegContext ppc) t) => RegAssign ppc f -> f t
getReg = (^. (Ctx.field @n))

ppcRegName :: MP.PPCReg v tp -> C.SolverSymbol
ppcRegName r = C.systemSymbol ("r!" ++ show (MC.prettyF r))

ppcRegStructType :: forall v
                  . ( MP.KnownVariant v )
                 => C.TypeRepr (MS.ArchRegStruct (MP.AnyPPC v))
ppcRegStructType =
  C.StructRepr (MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr ppcRegAssignment)

data PPCSymbolicException v = MissingRegisterInState (Some (MP.PPCReg v))

deriving instance Show (PPCSymbolicException v)

instance Typeable v => X.Exception (PPCSymbolicException v)

regIndexMap :: forall v
             . MP.KnownVariant v
            => MSB.RegIndexMap (MP.AnyPPC v)
regIndexMap = MSB.mkRegIndexMap assgn sz
  where
    assgn = ppcRegAssignment @v
    sz = Ctx.size (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr assgn))

lookupReg :: forall v ppc m f tp
           . (MP.KnownVariant v,
              ppc ~ MP.AnyPPC v,
              X.MonadThrow m)
          => MP.PPCReg v tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc)
          -> m (f (MS.ToCrucibleType tp))
lookupReg r asgn =
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn Ctx.! MSB.crucibleIndex pair)

updateReg :: forall v ppc m f tp
           . (MP.KnownVariant v,
               ppc ~ MP.AnyPPC v,
               X.MonadThrow m)
          => MP.PPCReg v tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc)
          -> m (Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc))
updateReg r upd asgn = do
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn & MapF.ixF (MSB.crucibleIndex pair) %~ upd)
