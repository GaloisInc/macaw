{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

AArch32 registers.

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
  , r0
  , r1
  , r2
  , r3
  , r4
  , r5
  , r6
  , r7
  , r8
  , r9
  , r10
  , r11
  , fp
  , r12
  , ip
  , r13
  , sp
  , r14
  , lr
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
-- semantics
--
-- See Note [ARM Registers]
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

-- | Local helper, not exported. The \"globals\" come before the GPRs in the
-- ArchRegContext.
type GlobalsCtx = MS.CtxToCrucibleType (PC.MapCtx ToMacawTypeWrapper LAG.SimpleGlobalsCtx)

type family CtxRepeat (n :: Nat) (c :: k) :: Ctx.Ctx k where
  CtxRepeat 0 c = Ctx.EmptyCtx
  CtxRepeat n c = CtxRepeat (n - 1) c Ctx.::> c

r0 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r0 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 0 (LCLM.LLVMPointerType 32))))

r1 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r1 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 1 (LCLM.LLVMPointerType 32))))

r2 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r2 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 2 (LCLM.LLVMPointerType 32))))

r3 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r3 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 3 (LCLM.LLVMPointerType 32))))

r4 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r4 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 4 (LCLM.LLVMPointerType 32))))

r5 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r5 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 5 (LCLM.LLVMPointerType 32))))

r6 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r6 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 6 (LCLM.LLVMPointerType 32))))

r7 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r7 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 7 (LCLM.LLVMPointerType 32))))

r8 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r8 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 8 (LCLM.LLVMPointerType 32))))

r9 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r9 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 9 (LCLM.LLVMPointerType 32))))

r10 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r10 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 10 (LCLM.LLVMPointerType 32))))

-- | Frame pointer, AKA 'fp'
r11 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r11 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 11 (LCLM.LLVMPointerType 32))))

-- | Frame pointer, AKA 'r11'
fp :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
fp = r11

-- | Intra-procedure call scratch register, AKA 'ip'
r12 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r12 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 12 (LCLM.LLVMPointerType 32))))

-- | Intra-procedure call scratch register, AKA 'r12'
ip :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
ip = r12

-- | Stack pointer, AKA 'sp'
r13 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r13 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 13 (LCLM.LLVMPointerType 32))))

-- | Stack pointer, AKA 'r13'
sp :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
sp = r13

-- | Link register, AKA 'lr'
r14 :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
r14 = Ctx.extendIndex (Ctx.nextIndex (Ctx.knownSize @_ @(GlobalsCtx Ctx.<+> CtxRepeat 14 (LCLM.LLVMPointerType 32))))

-- | Link register, AKA 'r14'
lr :: Ctx.Index (MS.MacawCrucibleRegTypes SA.AArch32) (LCLM.LLVMPointerType 32)
lr = r14

