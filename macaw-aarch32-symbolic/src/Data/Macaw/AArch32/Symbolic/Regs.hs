{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

AArch32 registers.

The symbolic execution (and the code discovery in macaw-aarch32) track a
superset of the user-visible architectural state, which only includes the GPRs
and SIMD registers.  The extended state includes low-level architectural details
referenced by the ASL semantics.

In asl-translator, the set of architectural state is referred to as the
"tracked" registers (or @allGlobalRefs@).  This is state that must be maintained
during code discovery and symbolic execution, which includes things like:

- The IT state
- Branch taken/not taken flags
- Various flags

Note that there is "untracked" state, which is architectural state referred to
in the semantics, but that is entirely local to an instruction.  These are
equivalent to local variables and do not appear in the post states of any
instructions.  We do not track those in the symbolic execution because they are
effectively inlined when we symbolically execute the ASL semantics into formulas
for semmc.

This module is meant to be imported qualified, as it exports many terse names.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.AArch32.Symbolic.Regs
  ( RegContext
  , aarch32RegAssignment
  , aarch32RegStructType
  , R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, Fp, R12, Ip, R13, Sp, R14, Lr, R15, Pc
  , V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15, V16
  , V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31
  , r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, fp, r12, ip, r13, sp, r14, lr, r15, pc
  , v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16
  , v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31
  ) where

import           GHC.TypeLits

import qualified Data.Functor.Identity as I
import           Data.Kind (Type)
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.CtxFuns as PC
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Proxy (Proxy(..))
import qualified What4.BaseTypes as WT

import qualified Language.ASL.Globals as LAG
import qualified SemMC.Architecture.AArch32 as SA
import qualified Data.Macaw.ARM.ARMReg as MAR

import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Types as CT

import qualified Data.Macaw.AArch32.Symbolic.Panic as AP

-- | All of the registers tracked in the AArch32 machine code model
--
-- Note that this set is significantly larger than the user-visible
-- architectural state and includes a large number of hidden state from the ASL
-- semantics, see the module-level documentation.
type RegContext = PC.MapCtx ToMacawTypeWrapper (LAG.SimpleGlobalsCtx Ctx.<+> LAG.GPRCtx Ctx.<+> LAG.SIMDCtx)
type instance MS.ArchRegContext SA.AArch32 = RegContext

data ToMacawTypeWrapper :: PC.TyFun WT.BaseType MT.Type -> Type
type instance PC.Apply ToMacawTypeWrapper t = BaseToMacawType t

aarch32RegAssignment :: Ctx.Assignment MAR.ARMReg RegContext
aarch32RegAssignment =
  I.runIdentity (PC.traverseMapCtx (Proxy @AsMacawReg) asARMReg (FC.fmapFC LAG.SimpleGlobalRef LAG.simpleGlobalRefs Ctx.<++> LAG.gprGlobalRefsSym Ctx.<++> LAG.simdGlobalRefsSym))

data AsMacawReg :: PC.TyFun Symbol MT.Type -> Type
type instance PC.Apply AsMacawReg s = BaseToMacawType (LAG.GlobalsType s)

asARMReg :: (Monad m) => LAG.GlobalRef s -> m (MAR.ARMReg (BaseToMacawType (LAG.GlobalsType s)))
asARMReg gr =
  case LAG.globalRefRepr gr of
    WT.BaseBoolRepr -> return (MAR.ARMGlobalBool gr)
    WT.BaseBVRepr _ -> return (MAR.ARMGlobalBV gr)
    WT.BaseStructRepr Ctx.Empty -> return MAR.ARMDummyReg
    tp -> AP.panic AP.AArch32 "asARMReg" ["Unexpected type: " ++ show tp]

type family BaseToMacawType (t :: WT.BaseType) :: MT.Type where
  BaseToMacawType WT.BaseBoolType = MT.BoolType
  BaseToMacawType (WT.BaseBVType n) = MT.BVType n
  BaseToMacawType (WT.BaseStructType Ctx.EmptyCtx) = MT.TupleType '[]

aarch32RegStructType :: CT.TypeRepr (MS.ArchRegStruct SA.AArch32)
aarch32RegStructType =
  CT.StructRepr (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr aarch32RegAssignment))

-- The following definitions for rN are tightly coupled to that of
-- ArchRegContext for AArch32. Unit tests in the test suite ensure that they are
-- consistent with regIndexMap (below).

type R0 = 36
type R1 = 37
type R2 = 38
type R3 = 39
type R4 = 40
type R5 = 41
type R6 = 42
type R7 = 43
type R8 = 44
type R9 = 45
type R10 = 46
-- | AKA 'Fp'
type R11 = 47
-- | AKA 'R11'
type Fp = 47
-- | AKA 'Ip'
type R12 = 48
-- | AKA 'R12'
type Ip = 48
-- | AKA 'Sp'
type R13 = 49
-- | AKA 'R13'
type Sp = 49
-- | AKA 'Lr'
type R14 = 50
-- | AKA 'R14'
type Lr = 50
-- | AKA 'Pc'
type R15 = 11
-- | AKA 'R15'
type Pc = 11
type V0 = 51
type V1 = 52
type V2 = 53
type V3 = 54
type V4 = 55
type V5 = 56
type V6 = 57
type V7 = 58
type V8 = 59
type V9 = 60
type V10 = 61
type V11 = 62
type V12 = 63
type V13 = 64
type V14 = 65
type V15 = 66
type V16 = 67
type V17 = 68
type V18 = 69
type V19 = 70
type V20 = 71
type V21 = 72
type V22 = 73
type V23 = 74
type V24 = 75
type V25 = 76
type V26 = 77
type V27 = 78
type V28 = 79
type V29 = 80
type V30 = 81
type V31 = 82

r0 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r0 = Ctx.natIndex @R0

r1 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r1 = Ctx.natIndex @R1

r2 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r2 = Ctx.natIndex @R2

r3 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r3 = Ctx.natIndex @R3

r4 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r4 = Ctx.natIndex @R4

r5 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r5 = Ctx.natIndex @R5

r6 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r6 = Ctx.natIndex @R6

r7 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r7 = Ctx.natIndex @R7

r8 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r8 = Ctx.natIndex @R8

r9 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r9 = Ctx.natIndex @R9

r10 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r10 = Ctx.natIndex @R10

-- | Frame pointer, AKA 'fp'
r11 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r11 = Ctx.natIndex @R11

-- | Frame pointer, AKA 'r11'
fp :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
fp = Ctx.natIndex @Fp

-- | Intra-procedure call scratch register, AKA 'ip'
r12 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r12 = Ctx.natIndex @R12

-- | Intra-procedure call scratch register, AKA 'r12'
ip :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
ip = Ctx.natIndex @Ip

-- | Stack pointer, AKA 'sp'
r13 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r13 = Ctx.natIndex @R13

-- | Stack pointer, AKA 'r13'
sp :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
sp = Ctx.natIndex @Sp

-- | Link register, AKA 'lr'
r14 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r14 = Ctx.natIndex @R14

-- | Link register, AKA 'r14'
lr :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
lr = Ctx.natIndex @Lr

-- | Program counter, AKA 'pc'
r15 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r15 = Ctx.natIndex @R15

-- | Program counter, AKA 'r15'
pc :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
pc = Ctx.natIndex @Pc

v0 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v0 = Ctx.natIndex @V0

v1 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v1 = Ctx.natIndex @V1

v2 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v2 = Ctx.natIndex @V2

v3 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v3 = Ctx.natIndex @V3

v4 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v4 = Ctx.natIndex @V4

v5 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v5 = Ctx.natIndex @V5

v6 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v6 = Ctx.natIndex @V6

v7 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v7 = Ctx.natIndex @V7

v8 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v8 = Ctx.natIndex @V8

v9 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v9 = Ctx.natIndex @V9

v10 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v10 = Ctx.natIndex @V10

v11 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v11 = Ctx.natIndex @V11

v12 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v12 = Ctx.natIndex @V12

v13 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v13 = Ctx.natIndex @V13

v14 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v14 = Ctx.natIndex @V14

v15 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v15 = Ctx.natIndex @V15

v16 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v16 = Ctx.natIndex @V16

v17 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v17 = Ctx.natIndex @V17

v18 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v18 = Ctx.natIndex @V18

v19 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v19 = Ctx.natIndex @V19

v20 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v20 = Ctx.natIndex @V20

v21 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v21 = Ctx.natIndex @V21

v22 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v22 = Ctx.natIndex @V22

v23 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v23 = Ctx.natIndex @V23

v24 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v24 = Ctx.natIndex @V24

v25 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v25 = Ctx.natIndex @V25

v26 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v26 = Ctx.natIndex @V26

v27 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v27 = Ctx.natIndex @V27

v28 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v28 = Ctx.natIndex @V28

v29 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v29 = Ctx.natIndex @V29

v30 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v30 = Ctx.natIndex @V30

v31 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 128)
v31 = Ctx.natIndex @V31

