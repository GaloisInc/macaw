{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

x86_64 registers.

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

module Data.Macaw.X86.Symbolic.Regs
  ( RegAssign
  , IP, GP, Flag, X87Status, X87Top, X87Tag, FPReg, YMM
  , Rip, Rax, Rcx, Rdx, Rbx, Rsp, Rbp, Rsi, Rdi
  , R8, R9, R10, R11, R12, R13, R14, R15
  , CF, PF, AF, ZF, SF, TF, IF, DF, OF
  , IE, DE, ZE, OE, UE, PE, EF, ES, C0, C1, C2, C3
  , Tag0, Tag1, Tag2, Tag3, Tag4, Tag5, Tag6, Tag7
  , St0, St1, St2, St3, St4, St5, St6, St7
  , Zmm0, Zmm1, Zmm2, Zmm3, Zmm4, Zmm5, Zmm6, Zmm7
  , Zmm8, Zmm9, Zmm10, Zmm11, Zmm12, Zmm13, Zmm14, Zmm15
  , rip, rax, rbx, rcx, rdx, rsp, rbp, rsi, rdi
  , r8, r9, r10, r11, r12, r13, r14, r15
  , cf, pf, af, zf, sf, tf, if_, df, of_
  , ie, de, ze, oe, ue, pe, ef, es, c0, c1, c2, c3, top
  , tag0, tag1, tag2, tag3, tag4, tag5, tag6, tag7
  , st0, st1, st2, st3, st4, st5, st6, st7
  , zmm0, zmm1, zmm2, zmm3, zmm4, zmm5, zmm6, zmm7
  , zmm8, zmm9, zmm10, zmm11, zmm12, zmm13, zmm14, zmm15
  , x86RegAssignment
  , x86RegTypes
  , x86RegName
  , x86RegStructType
  , lookupX86Reg
  , updateX86Reg
  , freshX86Reg
  , getReg
  ) where

import           Control.Lens ((^.),(%~),(&))
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC
import qualified Flexdis86.Register as F
import           GHC.TypeLits

import           Data.Macaw.Symbolic
import           Data.Macaw.Symbolic.Backend
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as M
import qualified Data.Macaw.X86.X86Reg as M

import qualified What4.Interface as WI
import qualified What4.InterpretedFloatingPoint as WIF
import qualified What4.Symbol as C

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel as MM

------------------------------------------------------------------------
-- Utilities for generating a type-level context with repeated elements.

type family CtxRepeat (n :: Nat) (c :: k) :: Ctx k where
  CtxRepeat  0 c = EmptyCtx
  CtxRepeat  n c = CtxRepeat  (n-1) c ::> c

class RepeatAssign (tp :: k) (ctx :: Ctx k) where
  repeatAssign :: (Int -> f tp) -> Assignment f ctx

instance RepeatAssign tp EmptyCtx where
  repeatAssign _ = Empty

instance RepeatAssign tp ctx => RepeatAssign tp (ctx ::> tp) where
  repeatAssign f =
    let r = repeatAssign f
     in r :> f (sizeInt (Ctx.size r))

------------------------------------------------------------------------
-- X86 Registers

type instance ArchRegContext M.X86_64
   =   (EmptyCtx ::> M.BVType 64)   -- IP
   <+> CtxRepeat 16 (M.BVType 64)   -- GP regs
   <+> CtxRepeat 9  M.BoolType      -- Flags
   <+> CtxRepeat 12  M.BoolType     -- X87 Status regs (x87 status word)
   <+> (EmptyCtx ::> M.BVType 3)    -- X87 top of the stack (x87 status word)
   <+> CtxRepeat 8 (M.BVType 2)     -- X87 tags
   <+> CtxRepeat 8 (M.BVType 80)    -- FP regs
   <+> CtxRepeat 16 (M.BVType 512)  -- ZMM regs

type RegAssign f = Assignment f (ArchRegContext M.X86_64)

-- The following definitions are tightly coupled to that of ArchRegContext for
-- X86_64. Unit tests in the test suite ensure that they are consistent with
-- x86RegAssignment (below).

type IP          = 0        -- 1
type Rip         = 0        -- 1
type GP n        = 1 + n    -- 16
type Rax         = GP 0
type Rcx         = GP 1
type Rdx         = GP 2
type Rbx         = GP 3
type Rsp         = GP 4
type Rbp         = GP 5
type Rsi         = GP 6
type Rdi         = GP 7
type R8          = GP 8
type R9          = GP 9
type R10         = GP 10
type R11         = GP 11
type R12         = GP 12
type R13         = GP 13
type R14         = GP 14
type R15         = GP 15
type Flag n      = 17 + n   -- 9
type CF          = Flag 0
type PF          = Flag 1
type AF          = Flag 2
type ZF          = Flag 3
type SF          = Flag 4
type TF          = Flag 5
type IF          = Flag 6
type DF          = Flag 7
type OF          = Flag 8
type X87Status n = 26 + n   -- 12
type IE          = X87Status 0
type DE          = X87Status 1
type ZE          = X87Status 2
type OE          = X87Status 3
type UE          = X87Status 4
type PE          = X87Status 5
type EF          = X87Status 6
type ES          = X87Status 7
type C0          = X87Status 8
type C1          = X87Status 9
type C2          = X87Status 10
type C3          = X87Status 11
type X87Top      = 38       -- 1
type X87Tag n    = 39 + n   -- 8
type Tag0        = X87Tag 0
type Tag1        = X87Tag 1
type Tag2        = X87Tag 2
type Tag3        = X87Tag 3
type Tag4        = X87Tag 4
type Tag5        = X87Tag 5
type Tag6        = X87Tag 6
type Tag7        = X87Tag 7
type FPReg n     = 47 + n   -- 8
type St0         = FPReg 0
type St1         = FPReg 1
type St2         = FPReg 2
type St3         = FPReg 3
type St4         = FPReg 4
type St5         = FPReg 5
type St6         = FPReg 6
type St7         = FPReg 7
type YMM n       = 55 + n   -- 16
type Zmm0         = YMM 0
type Zmm1         = YMM 1
type Zmm2         = YMM 2
type Zmm3         = YMM 3
type Zmm4         = YMM 4
type Zmm5         = YMM 5
type Zmm6         = YMM 6
type Zmm7         = YMM 7
type Zmm8         = YMM 8
type Zmm9         = YMM 9
type Zmm10        = YMM 10
type Zmm11        = YMM 11
type Zmm12        = YMM 12
type Zmm13        = YMM 13
type Zmm14        = YMM 14
type Zmm15        = YMM 15

rip :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rip = Ctx.natIndex @Rip

rax :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rax = Ctx.natIndex @Rax

rcx :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rcx = Ctx.natIndex @Rcx

rdx :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rdx = Ctx.natIndex @Rdx

rbx :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rbx = Ctx.natIndex @Rbx

rsp :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rsp = Ctx.natIndex @Rsp

rbp :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rbp = Ctx.natIndex @Rbp

rsi :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rsi = Ctx.natIndex @Rsi

rdi :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
rdi = Ctx.natIndex @Rdi

r8 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r8 = Ctx.natIndex @R8

r9 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r9 = Ctx.natIndex @R9

r10 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r10 = Ctx.natIndex @R10

r11 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r11 = Ctx.natIndex @R11

r12 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r12 = Ctx.natIndex @R12

r13 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r13 = Ctx.natIndex @R13

r14 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r14 = Ctx.natIndex @R14

r15 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 64)
r15 = Ctx.natIndex @R15

-- | Carry flag
cf :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
cf = Ctx.natIndex @CF

-- | Parity flag
pf :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
pf = Ctx.natIndex @PF

-- | Auxiliary carry flag
af :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
af = Ctx.natIndex @AF

-- | Zero flag
zf :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
zf = Ctx.natIndex @ZF

-- | Sign flag
sf :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
sf = Ctx.natIndex @SF

-- | Trap flag
tf :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
tf = Ctx.natIndex @TF

-- | Interrupt enable flag
if_ :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
if_ = Ctx.natIndex @IF

-- | Direction flag
df :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
df = Ctx.natIndex @DF

-- | Overflow flag
of_ :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
of_ = Ctx.natIndex @OF

-- | Invalid operation
ie :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
ie = Ctx.natIndex @IE

-- | Denormalized operand
de :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
de = Ctx.natIndex @DE

-- | Zero divide
ze :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
ze = Ctx.natIndex @ZE

-- | Overflow
oe :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
oe = Ctx.natIndex @OE

-- | Underflow
ue :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
ue = Ctx.natIndex @UE

-- | Precision
pe :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
pe = Ctx.natIndex @PE

ef :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
ef = Ctx.natIndex @EF

es :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
es = Ctx.natIndex @ES

c0 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
c0 = Ctx.natIndex @C0

c1 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
c1 = Ctx.natIndex @C1

c2 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
c2 = Ctx.natIndex @C2

c3 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) C.BoolType
c3 = Ctx.natIndex @C3

top :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 3)
top = Ctx.natIndex @X87Top

tag0 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag0 = Ctx.natIndex @Tag0

tag1 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag1 = Ctx.natIndex @Tag1

tag2 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag2 = Ctx.natIndex @Tag2

tag3 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag3 = Ctx.natIndex @Tag3

tag4 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag4 = Ctx.natIndex @Tag4

tag5 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag5 = Ctx.natIndex @Tag5

tag6 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag6 = Ctx.natIndex @Tag6

tag7 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 2)
tag7 = Ctx.natIndex @Tag7

st0 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st0 = Ctx.natIndex @St0

st1 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st1 = Ctx.natIndex @St1

st2 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st2 = Ctx.natIndex @St2

st3 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st3 = Ctx.natIndex @St3

st4 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st4 = Ctx.natIndex @St4

st5 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st5 = Ctx.natIndex @St5

st6 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st6 = Ctx.natIndex @St6

st7 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 80)
st7 = Ctx.natIndex @St7

zmm0 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm0  = Ctx.natIndex @Zmm0

zmm1 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm1  = Ctx.natIndex @Zmm1

zmm2 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm2  = Ctx.natIndex @Zmm2

zmm3 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm3  = Ctx.natIndex @Zmm3

zmm4 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm4  = Ctx.natIndex @Zmm4

zmm5 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm5  = Ctx.natIndex @Zmm5

zmm6 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm6  = Ctx.natIndex @Zmm6

zmm7 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm7  = Ctx.natIndex @Zmm7

zmm8 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm8  = Ctx.natIndex @Zmm8

zmm9 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm9  = Ctx.natIndex @Zmm9

zmm10 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm10 = Ctx.natIndex @Zmm10

zmm11 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm11 = Ctx.natIndex @Zmm11

zmm12 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm12 = Ctx.natIndex @Zmm12

zmm13 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm13 = Ctx.natIndex @Zmm13

zmm14 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm14 = Ctx.natIndex @Zmm14

zmm15 :: Ctx.Index (MacawCrucibleRegTypes M.X86_64) (MM.LLVMPointerType 512)
zmm15 = Ctx.natIndex @Zmm15

------------------------------------------------------------------------
-- Functions

getReg ::
  forall n t f. (Idx n (ArchRegContext M.X86_64) t) => RegAssign f -> f t
getReg x = x ^. (field @n)

x86RegName' :: M.X86Reg tp -> String
x86RegName' M.X86_IP     = "ip"
x86RegName' (M.X86_GP r) = show r
x86RegName' (M.X86_FlagReg r) = show r
x86RegName' r@(M.X87_StatusReg _) = show r
x86RegName' M.X87_TopReg = "x87Top"
x86RegName' (M.X87_TagReg r) = "x87Tag" ++ show r
x86RegName' r@(M.X87_FPUReg _) = show r
x86RegName' r@(M.X86_ZMMReg _) = show r

x86RegName :: M.X86Reg tp -> C.SolverSymbol
x86RegName r = C.systemSymbol $ "r!" ++ x86RegName' r

gpReg :: Int -> M.X86Reg (M.BVType 64)
gpReg = M.X86_GP . F.Reg64 . fromIntegral

-- | The x86 flag registers that are directly supported by Macaw.
flagRegs :: Assignment M.X86Reg (CtxRepeat 9 M.BoolType)
flagRegs =
  Empty :> M.CF :> M.PF :> M.AF :> M.ZF :> M.SF :> M.TF :> M.IF :> M.DF :> M.OF

x87_statusRegs :: Assignment M.X86Reg (CtxRepeat 12 M.BoolType)
x87_statusRegs =
     (repeatAssign (M.X87_StatusReg . fromIntegral)
        :: Assignment M.X86Reg (CtxRepeat 11 M.BoolType))
  :> M.X87_StatusReg 14

-- | This contains an assignment that stores the register associated with each index in the
-- X86 register structure.
x86RegAssignment :: Assignment M.X86Reg (ArchRegContext M.X86_64)
x86RegAssignment =
  Empty :> M.X86_IP
  <++> (repeatAssign gpReg :: Assignment M.X86Reg (CtxRepeat 16 (M.BVType 64)))
  <++> flagRegs
  <++> x87_statusRegs
  <++> (Empty :> M.X87_TopReg)
  <++> (repeatAssign (M.X87_TagReg . fromIntegral)    :: Assignment M.X86Reg (CtxRepeat  8 (M.BVType 2)))
  <++> (repeatAssign (M.X87_FPUReg . F.mmxReg . fromIntegral) :: Assignment M.X86Reg (CtxRepeat  8 (M.BVType 80)))
  <++> (repeatAssign (M.X86_ZMMReg . fromIntegral)
        :: Assignment M.X86Reg (CtxRepeat 16 (M.BVType 512)))

x86RegTypes :: Ctx.Assignment C.TypeRepr (CtxToCrucibleType (ArchRegContext M.X86_64))
x86RegTypes = typeCtxToCrucible $ fmapFC M.typeRepr x86RegAssignment

x86RegStructType :: C.TypeRepr (ArchRegStruct M.X86_64)
x86RegStructType = C.StructRepr x86RegTypes

regIndexMap :: RegIndexMap M.X86_64
regIndexMap = mkRegIndexMap x86RegAssignment $ Ctx.size x86RegTypes

{- | Lookup a Macaw register in a Crucible assignemnt.
This function returns "Nothing" if the input register is not represented
in the assignment.  This means that either the input register is malformed,
or we haven't modelled this register for some reason. -}
lookupX86Reg ::
  M.X86Reg t                                    {- ^ Lookup this register -} ->
  Assignment f (MacawCrucibleRegTypes M.X86_64) {- ^ Assignment -} ->
  Maybe (f (ToCrucibleType t))  {- ^ The value of the register -}
lookupX86Reg r asgn =
  do pair <- MapF.lookup r regIndexMap
     return (asgn Ctx.! crucibleIndex pair)

updateX86Reg ::
  M.X86Reg t ->
  (f (ToCrucibleType t) -> f (ToCrucibleType t)) ->
  Assignment f (MacawCrucibleRegTypes M.X86_64) {- ^Update this assignment -} ->
  Maybe (Assignment f (MacawCrucibleRegTypes M.X86_64))
updateX86Reg r upd asgn =
  do pair <- MapF.lookup r regIndexMap
     return (asgn & ixF (crucibleIndex pair) %~ upd)
     -- return (adjust upd (crucibleIndex pair) asgn)

freshX86Reg :: C.IsSymInterface sym =>
  sym -> M.X86Reg t -> IO (C.RegValue' sym (ToCrucibleType t))
freshX86Reg sym r =
  C.RV <$> freshValue sym (show r) (Just (C.knownNat @64))  (M.typeRepr r)

freshValue ::
  (C.IsSymInterface sym, 1 <= ptrW) =>
  sym ->
  String {- ^ Name for fresh value -} ->
  Maybe (C.NatRepr ptrW) {- ^ Width of pointers; if nothing, allocate as bits -} ->
  M.TypeRepr tp {- ^ Type of value -} ->
  IO (C.RegValue sym (ToCrucibleType tp))
freshValue sym str w ty =
  case ty of
    M.BVTypeRepr y ->
      case testEquality y =<< w of

        Just Refl ->
          do nm_base <- symName (str ++ "_base")
             nm_off  <- symName (str ++ "_off")
             base    <- WI.freshNat sym nm_base
             offs    <- WI.freshConstant sym nm_off (C.BaseBVRepr y)
             return (MM.LLVMPointer base offs)

        Nothing ->
          do nm   <- symName str
             base <- WI.natLit sym 0
             offs <- WI.freshConstant sym nm (C.BaseBVRepr y)
             return (MM.LLVMPointer base offs)

    M.FloatTypeRepr fi -> do
      nm <- symName str
      WIF.freshFloatConstant sym nm $ floatInfoToCrucible fi

    M.BoolTypeRepr ->
      do nm <- symName str
         WI.freshConstant sym nm C.BaseBoolRepr

    M.TupleTypeRepr {} -> crash [ "Unexpected symbolic tuple:", show str ]
    M.VecTypeRepr {} -> crash [ "Unexpected symbolic vector:", show str ]

  where
  symName x =
    case C.userSymbol ("macaw_" ++ x) of
      Left err -> crash [ "Invalid symbol name:", show x, show err ]
      Right a -> return a

  crash xs =
    case xs of
      [] -> crash ["(unknown)"]
      y : ys -> fail $ unlines $ ("[freshX86Reg] " ++ y)
                               : [ "*** " ++ z | z <- ys ]
