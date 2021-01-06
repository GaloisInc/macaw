{-|
 Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines various types on top of X86Generator to defined
semantics of X86 instructions.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wwarn #-}
module Data.Macaw.X86.Monad
  ( -- * Type
    XMMType
  , YMMType
  , RepValSize(..)
  , repValHasSupportedWidth
  , repValSizeByteCount
  , repValSizeMemRepr
  , Data.Macaw.Types.FloatInfoRepr(..)
  , Data.Macaw.Types.floatInfoBits
    -- * RegisterView
  , RegisterView
  , RegisterViewType(..)
  , registerViewRead
  , registerViewWrite
  , registerViewBase
  , registerViewSize
  , registerViewReg
  , registerViewType
    -- * Location
  , Location(..)
  , ppLocation
  , x87reg_mmx
  , fullRegister
  , subRegister
  , reg_low8
  , reg_high8
  , reg_low16
  , reg_low32
  , reg_low128_sse
  , reg_low128_avx
  , reg_high128

  , cf_loc
  , pf_loc
  , af_loc
  , zf_loc
  , sf_loc
  , tf_loc
  , if_loc
  , df_loc
  , of_loc
    -- X87
  , c0_loc
  , c1_loc
  , c2_loc
  , c3_loc

  , packWord
  , unpackWord
  -- ** Registers
  , rip
  , rax, rbx, rcx, rdx, rsp, rbp, rsi, rdi
  , eax, ebx, ecx, edx
  , ax, bx, cx, dx
  , al, dl
  , ah
  , ymm_preserve
  , ymm_zero
  , xmm_sse
  , xmm_avx
  , xmmOwner
    -- * Value operations
  , bvLit
  , (.=.)
  , (.=/=.)
  , mux
  , true
  , false
  , boolNot
  , boolXor
  , bvKLit
  , bvNeg
  , (.+)
  , uadd_overflows
  , uadc_overflows
  , sadd_overflows
  , sadc_overflows
  , (.-)
  , usub_overflows
  , ssub_overflows
  , ssbb_overflows
  , bvSlt
  , bvUlt
  , bvUle
  , bvShl
  , bvShr
  , bvBit
  , (.*)
  , (.&&.)
  , (.||.)
  , bvComplement
  , (.&.)
  , (.|.)
  , bvXor
  , bvSar
  , bvRol
  , bvRor
  , bvTrunc'
  , bvTrunc
--  , bitcast
  , msb
  , least_byte
  , least_nibble
  , is_zero
  , bsf
  , bsr
  , uext
  , uext'
  , sext
  , sext'
  , bvCat
  , bvSplit
  , vectorize2
  , bvVectorize
  , bvUnvectorize
    -- * Semantics
  , SIMDWidth(..)
  , make_undefined
  , set_undefined
  , getReg
  , get
  , (.=)
  , modify
    -- * Other
  , Data.Macaw.X86.ArchTypes.X86PrimFn(..)
  , Data.Macaw.X86.ArchTypes.X86TermStmt(..)
  , Data.Macaw.X86.Generator.X86Generator
  , Data.Macaw.X86.Generator.Expr
  , Data.Macaw.X86.Generator.eval
  , Data.Macaw.X86.Generator.evalArchFn
  , Data.Macaw.X86.Generator.addArchTermStmt
  , even_parity
  , x87Push
  , x87Pop
    -- * SupportedBVWidth
  , SupportedBVWidth
    -- * Re-exports
  , type (TypeLits.<=)
  , type Flexdis86.Sizes.SizeConstraint(..)
  ) where

import           Control.Exception
import           Control.Lens hiding ((.=))
import           Control.Monad
import qualified Data.Bits as Bits
import           Data.Macaw.CFG
import           Data.Macaw.Types
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import qualified Flexdis86 as F
import           Flexdis86.Sizes (SizeConstraint(..))
import           GHC.TypeLits as TypeLits
import           Prettyprinter as PP


import           Data.Macaw.X86.ArchTypes
import           Data.Macaw.X86.Generator
import           Data.Macaw.X86.X86Reg (X86Reg(..))
import qualified Data.Macaw.X86.X86Reg as R

type XMMType    = BVType 128
type YMMType    = BVType 256

ltProof :: forall f n m . (n+1 <= m) => f n -> f m -> LeqProof n m
ltProof _ _ = leqTrans lt LeqProof
  where lt :: LeqProof n (n+1)
        lt = leqAdd LeqProof n1

------------------------------------------------------------------------
-- Sub registers
--
-- See comments above 'registerViewRead'.

-- | The different kinds of register views.
--
-- We introduce this "tag" type, vs embedding the read and write
-- functions directly in the 'RegisterView', in order to reify the
-- read and write functions: these tags can be inspected at run time,
-- but the corresponding read and write functions cannot. The
-- 'registerViewRead' and 'registerViewWrite' functions below map a
-- 'RegisterView' to it's corresponding read and write functions,
-- using the constraints embedded in the 'RegisterViewType' tag.
--
-- We could optimize the common case of full registers by introducing
-- a @IdentityView@ of type @RegisterViewType cl 0
-- (R.registerclassbits cl)@ whose read view is @\x -> x@ and write
-- view is @\x y -> y@.
data RegisterViewType m (b :: Nat) (n :: Nat)
  = ( 1 <= n
    , n <= m
    )
    => DefaultView
  | ( 1 <= n
    , 1 <= m
    , n <= m
    , 1 <= m - n
    , m - n <= m
    , ((m - n) + n) ~ m
    , b ~ 0
    )
    => OneExtendOnWrite
  | ( 1 <= n
    , 1 <= m
    , n <= m
    , 1 <= m - n
    , m - n <= m
    , ((m - n) + n) ~ m
    , b ~ 0
    )
    => ZeroExtendOnWrite

compareRegisterViewType :: RegisterViewType w b n -> RegisterViewType w' b' n' -> Ordering
DefaultView `compareRegisterViewType` DefaultView = EQ
DefaultView `compareRegisterViewType` _ = LT
_ `compareRegisterViewType` DefaultView = GT
OneExtendOnWrite `compareRegisterViewType` OneExtendOnWrite = EQ
OneExtendOnWrite `compareRegisterViewType` _ = LT
_ `compareRegisterViewType` OneExtendOnWrite = GT
ZeroExtendOnWrite `compareRegisterViewType` ZeroExtendOnWrite = EQ

instance Ord (RegisterViewType w b n) where
  compare = compareRegisterViewType

instance Eq (RegisterViewType w b n) where
  rvt == rvt'
    | EQ <- rvt `compareRegisterViewType` rvt' = True
    | otherwise = False


-- | A view into a register / a subregister.
data RegisterView w b n
  = (1 <= n, b + n <= w)
 => RegisterView
    { _registerViewBase :: NatRepr b
    , _registerViewSize :: NatRepr n
    , _registerViewReg :: X86Reg (BVType w)
    , _registerViewType :: RegisterViewType w b n
    }

compareRegisterView :: RegisterView w b n -> RegisterView w' b' n' -> Ordering
compareRegisterView rv rv' =
  case ( _registerViewBase rv `compareF` _registerViewBase rv'
       , _registerViewSize rv `compareF` _registerViewSize rv'
       , _registerViewReg rv `compareF` _registerViewReg rv'
       ) of
    (LTF, _, _) -> LT
    (GTF, _, _) -> GT
    (EQF, LTF, _) -> LT
    (EQF, GTF, _) -> GT
    (EQF, EQF, LTF) -> LT
    (EQF, EQF, GTF) -> GT
    (EQF, EQF, EQF) ->
      _registerViewType rv `compareRegisterViewType` _registerViewType rv'

instance Eq (RegisterView w b n) where
  x == y = compare x y == EQ

instance Ord (RegisterView w b n) where
  compare = compareRegisterView

-- * Destructors for 'RegisterView's.

registerViewBase :: RegisterView w b n -> NatRepr b
registerViewBase = _registerViewBase

registerViewSize :: RegisterView w b n -> NatRepr n
registerViewSize = _registerViewSize

registerViewReg :: RegisterView w b n -> X86Reg (BVType w)
registerViewReg = _registerViewReg

registerViewType :: RegisterView w b n -> RegisterViewType w b n
registerViewType = _registerViewType

-- * Read and write views for 'RegisterView's.

-- | Extract 'n' bits starting at base 'b'.
defaultRegisterViewRead
  :: forall b n m ids
  .  ( 1 <= n
     , n <= m
     )
  => NatRepr b
  -> NatRepr n
  -> X86Reg (BVType m)
  -> Expr ids (BVType m)
  -> Expr ids (BVType n)
defaultRegisterViewRead b n _rn v0
  | LeqProof <- leqTrans (LeqProof :: LeqProof 1 n) (LeqProof :: LeqProof n m) =
    bvTrunc n $ v0 `bvShr` bvLit (typeWidth v0) (intValue b)

-- | Read a register via a view.
--
-- The read and write operations specify how to read and write a
-- subregister value based on the current value @v0@ in the full
-- register. The write operation also depends on the new subregister
-- value @v@ to be written.
--
-- See 'defaultRegisterViewRead' and 'defaultRegisterViewWrite'
-- implement the common case (e.g. for @ax@ as a subregister of
-- @rax@).
--
-- The special cases motivating introduction of the 'RegisterView'
-- data type are:
--
-- * 32-bit subregisters of 64-bit general purpose registers
--   (e.g. @eax@ as a subregister of @rax@), where the high-order 32
--   bits should be zeroed out on writes
--
-- * 64-bit mmx subregisters of x87 registers, where the high-order 16
--   bits should be oned out on writes.
--
-- Note that some instructions, such as @movss@ and @movsd@, specify
-- what appears to be special treatment of subregisters as part of
-- their semantics. We don't expect these *explicit* instruction
-- semantics to be implemented using 'RegisterView'. Rather,
-- 'RegisterView' is intended to implement the *implicit* special
-- treatment of some aliased registers, namely the two cases mentioned
-- above. (But this distinction is arbitrary, and we could simplify
-- some semantic implementations by treating the lower-half of an XMM
-- register as a named subregister, using a 'RegisterView').
registerViewRead
  :: RegisterView m b n
  -> Expr ids (BVType m)
  -> Expr ids (BVType n)
registerViewRead v =
  case registerViewType v of
    DefaultView -> defaultRegisterViewRead b n rn
    OneExtendOnWrite -> defaultRegisterViewRead b n rn
    ZeroExtendOnWrite -> defaultRegisterViewRead b n rn
  where
    b  = _registerViewBase v
    n  = _registerViewSize v
    rn = _registerViewReg v

-- | Update the 'n' bits starting at base 'b', leaving other bits
-- unchanged.
--
-- Assumes a big-endian 'IsValue' semantics.
defaultRegisterViewWrite
  :: forall b m n ids
  . ( 1 <= n
    , n <= m
    )
  => NatRepr b
  -> NatRepr n
  -> X86Reg (BVType m)
  -> Expr ids (BVType m)
     -- ^ Value being modified
  -> Expr ids (BVType n)
     -- ^ Value to write
  -> Expr ids (BVType m)
defaultRegisterViewWrite b n rn v0 write_val
  | LeqProof <- leqTrans (LeqProof :: LeqProof 1 n) (LeqProof :: LeqProof n m) =
  -- Truncation 'bvTrunc' requires that the result vector has non-zero
  -- length, so we build the concatenation
  --
  --   h ++ m ++ l
  --
  -- using bitwise OR:
  --
  --   (h ++ 0^|m ++ l|)     ||
  --   (0^|h| ++ m ++ 0^|l|) ||
  --   (0^|h ++ m| ++ l)
  -- highOrderBits  .|. lowOrderBits
  let -- Generate the mask for the new bits
      myMask = maxUnsigned n `Bits.shiftL` fromInteger (intValue b)
      -- Generate max for old bits.
      notMyMask = Bits.complement myMask
      prevBits = v0 .&. bvLit w notMyMask
      w = typeWidth v0
      cl = typeWidth rn
      b' = intValue b
      middleOrderBits = uext cl write_val `bvShl` bvLit cl b'
   in prevBits .|. middleOrderBits


-- | Write a register via a view.
registerViewWrite
  :: RegisterView w b x1
  -> Expr ids (BVType w)
  -> Expr ids (BVType x1)
  -> Expr ids (BVType w)
registerViewWrite rv =
  case _registerViewType rv of
    DefaultView
      -- Just write the full register if possible
      | Just Refl <- b `testEquality` n0
      , Just Refl <- n `testEquality` typeWidth rn
      , DefaultView <- _registerViewType rv -> \ _v0 v -> v
      -- Otherwise use the defaultRegisterViewWrite
      | otherwise -> defaultRegisterViewWrite b n rn
    OneExtendOnWrite ->
      let ones = bvComplement (bvLit (cl `subNat` n) 0)
       in constUpperBitsRegisterViewWrite n ones rn
    ZeroExtendOnWrite ->
      let zeros = bvLit (cl `subNat` n) 0
       in constUpperBitsRegisterViewWrite n zeros rn
  where
    b = _registerViewBase rv
    n = _registerViewSize rv
    rn = _registerViewReg rv
    cl = typeWidth rn

constUpperBitsRegisterViewWrite
  :: (1 <= b, 1 <= e, (b + e) ~ f)
  => NatRepr a
  -> Expr ids (BVType b)
  -- ^ Constant bits.
  -> X86Reg (BVType c)
  -> Expr ids (BVType d)
  -> Expr ids (BVType e)
  -> Expr ids (BVType f)
constUpperBitsRegisterViewWrite _n c _rn _v0 v = bvCat c v

-- | The view for subregisters which are a slice of a full register.
sliceRegisterView
  :: ( 1     <= n
     , 1     <= m
     , n     <= m
     , b + n <= m
     )
  => NatRepr b
  -> NatRepr n
  -> X86Reg (BVType m)
  -> RegisterView m b n
sliceRegisterView b n rn =
  RegisterView
    { _registerViewBase = b
    , _registerViewSize = n
    , _registerViewReg = rn
    , _registerViewType = DefaultView
    }

-- | The view for 32-bit general purpose and mmx registers.
--
-- These are the special / weird sub registers where the upper bits of
-- the underlying full register are implicitly set to a constant on
-- writes.
constUpperBitsOnWriteRegisterView
  :: ( 1 <= n
     , n <= w
     )
  => NatRepr n
  -> RegisterViewType w 0 n
  -> X86Reg (BVType w)
  -> RegisterView w 0 n
constUpperBitsOnWriteRegisterView n rt rn  =
  RegisterView
    { _registerViewBase = n0
    , _registerViewSize = n
    , _registerViewReg = rn
    , _registerViewType = rt
    }

------------------------------------------------------------------------
-- Location

-- | This returns the type associated with values that can be read
-- or assigned for the semantics monad.
data Location addr (tp :: Type) where
  -- | A location in the virtual address space of the process.
  MemoryAddr :: !addr -> !(MemRepr tp) -> Location addr tp

  FullRegister :: !(X86Reg tp)
               -> Location addr tp

  Register :: !(RegisterView m b n)
           -> Location addr (BVType n)

  -- | The register stack: the argument is an offset from the stack
  -- top, so X87Register 0 is the top, X87Register 1 is the second,
  -- and so forth.
  X87StackRegister :: !Int
                   -> Location addr (FloatBVType X86_80Float)

------------------------------------------------------------------------
-- Location

-- | Type for addresses.
type AddrExpr ids = Expr ids (BVType 64)

type ImpLocation ids tp = Location (AddrExpr ids) tp

getX87Top :: X86Generator st_s ids Int
getX87Top = do
  top_val <- getRegValue X87_TopReg
  case top_val of
    BVValue _ (fromInteger -> topv) ->
      return topv
    _ -> fail $ "Unsupported value for top register " ++ show (pretty top_val)

getX87Offset :: Int -> X86Generator st_s ids Int
getX87Offset i = do
  topv <- getX87Top
  unless (0 <= topv + i && topv + i <= 7) $ do
    fail $ "Illegal floating point index"
  return $! topv + i

getReg :: X86Reg tp -> X86Generator st_s ids (Expr ids tp)
getReg r = ValueExpr <$> getRegValue r

-- | Assign a value to a location
setLoc :: forall ids st_s tp
       .  ImpLocation ids tp
       -> Value X86_64 ids tp
       -> X86Generator st_s ids ()
setLoc loc v =
  case loc of
   MemoryAddr w tp -> do
     addr <- eval w
     addStmt $ WriteMem addr tp v
   FullRegister r -> do
     setReg r v
   Register (rv :: RegisterView m b n) -> do
     let r = registerViewReg rv
     v0 <- getReg r
     v1 <- eval $ registerViewWrite rv v0 (ValueExpr v)
     setReg r v1
   X87StackRegister i -> do
     off <- getX87Offset i
     setReg (X87_FPUReg (F.mmxReg (fromIntegral off))) v

------------------------------------------------------------------------
-- Semantics

-- Equality and ordering.


instance Eq addr => EqF (Location addr) where
  MemoryAddr addr tp `eqF` MemoryAddr addr' tp'
    | Just Refl <- testEquality tp tp' = addr == addr'
  Register rv `eqF` Register rv'
    | EQ <- rv `compareRegisterView` rv' = True
  X87StackRegister i `eqF` X87StackRegister i' = i == i'
  _ `eqF` _ = False

instance Eq addr => Eq (Location addr tp) where
  (==) = eqF

-- | Pretty print 'Location'.
--
-- Note: this pretty printer ignores the embedded view functions in
-- 'RegisterView's, so the pretty printed value only indicates which
-- bits are in the view, not how the view is actually defined
--
-- Going back to pretty names for subregisters is pretty ad hoc;
-- see table at http://stackoverflow.com/a/1753627/470844. E.g.,
-- instead of @%ah@, we produce @%rax[8:16]@.
ppLocation :: forall addr tp ann. (addr -> Doc ann) -> Location addr tp -> Doc ann
ppLocation ppAddr loc = case loc of
  MemoryAddr addr _tr -> ppAddr addr
  Register rv -> ppReg rv
  FullRegister r -> "%" <> viaShow r
  X87StackRegister i -> "x87_stack@" <> viaShow i
  where
    -- | Print subrange as Python-style slice @<location>[<low>:<high>]@.
    --
    -- The low bit is inclusive and the high bit is exclusive, but I
    -- can't bring myself to generate @<reg>[<low>:<high>)@ :)
    ppReg :: RegisterView w n cl -> Doc ann
    ppReg rv =
      pretty $ "%" ++ show (_registerViewReg rv) ++
        if b == 0 && s == (fromIntegral $ intValue (typeWidth $ _registerViewReg rv))
        then ""
        else "[" ++ show b ++ ":" ++ show s ++ "]"
      where
        b = intValue $ _registerViewBase rv
        s = intValue $ _registerViewSize rv

------------------------------------------------------------------------
-- Register-location smart constructors.

-- | Full register location.
fullRegister :: X86Reg tp
             -> Location addr tp
fullRegister = FullRegister

-- | Subregister location for simple subregisters.
--
-- I.e., a subregister which reads and writes @n@ bits at offset @b@,
-- and preserves remaining bits on writes.
subRegister
  :: ( 1 <= n
     , 1 <= m
     , n <= m
     , b + n <= m
     )
  => NatRepr b
  -> NatRepr n
  -> X86Reg (BVType m)
  -> Location addr (BVType n)
subRegister b n = Register . sliceRegisterView b n

-- | The view for 32-bit general purpose and mmx registers.
--
-- These are the special / weird sub registers where the upper bits of
-- the underlying full register are implicitly set to a constant on
-- writes.
constUpperBitsOnWriteRegister ::
  ( 1 <= n
  , n <= m
  )
  => NatRepr n
  -> RegisterViewType m 0 n
  -> X86Reg (BVType m)
  -> Location addr (BVType n)
constUpperBitsOnWriteRegister n rt =
  Register . constUpperBitsOnWriteRegisterView n rt

------------------------------------------------------------------------
-- Operations on locations.

instance HasRepr (Location addr) TypeRepr where
  typeRepr (MemoryAddr _ tp) = typeRepr tp
  typeRepr (FullRegister r)  = typeRepr r
  typeRepr (Register rv@RegisterView{}) = BVTypeRepr $ _registerViewSize rv
  typeRepr (X87StackRegister _) = knownRepr

------------------------------------------------------------------------
-- Specific locations.

-- | CF flag
cf_loc :: Location addr BoolType
cf_loc = fullRegister R.CF

-- | PF flag
pf_loc :: Location addr BoolType
pf_loc = fullRegister R.PF

-- | AF flag
af_loc :: Location addr BoolType
af_loc = fullRegister R.AF

-- | ZF flag
zf_loc :: Location addr BoolType
zf_loc = fullRegister R.ZF

-- | SF flag
sf_loc :: Location addr BoolType
sf_loc = fullRegister R.SF

-- | TF flag
tf_loc :: Location addr BoolType
tf_loc = fullRegister R.TF

-- | IF flag
if_loc :: Location addr BoolType
if_loc = fullRegister R.IF

-- | DF flag
df_loc :: Location addr BoolType
df_loc = fullRegister R.DF

-- | OF flag
of_loc :: Location addr BoolType
of_loc = fullRegister R.OF

-- | x87 flags
c0_loc, c1_loc, c2_loc, c3_loc :: Location addr BoolType
c0_loc = fullRegister R.X87_C0
c1_loc = fullRegister R.X87_C1
c2_loc = fullRegister R.X87_C2
c3_loc = fullRegister R.X87_C3

-- | Return MMX register corresponding to x87 register.
--
-- An MMX register is the low 64-bits of an x87 register. These
-- registers have special semantics, defined in Volume 1 of the Intel
-- x86 manual: on write,the upper 16 bits of the underlying x87
-- register are oned out!
x87reg_mmx :: X86Reg R.X87_FPU -> Location addr (BVType 64)
x87reg_mmx r = constUpperBitsOnWriteRegister n64 OneExtendOnWrite r

-- | Return low 32-bits of register e.g. rax -> eax
--
-- These subregisters have special semantics, defined in Volume 1 of
-- the Intel x86 manual: on write, the upper 32 bits are zeroed out!
reg_low32 :: X86Reg R.GP -> Location addr (BVType 32)
reg_low32 r = constUpperBitsOnWriteRegister n32 ZeroExtendOnWrite r

-- | Return low 16-bits of register e.g. rax -> ax
reg_low16 :: X86Reg R.GP -> Location addr (BVType 16)
reg_low16 r = subRegister n0 n16 r

-- | Return low 8-bits of register e.g. rax -> al
reg_low8 :: X86Reg R.GP -> Location addr (BVType 8)
reg_low8 r = subRegister n0 n8 r

-- | Return bits 8-15 of the register e.g. rax -> ah
reg_high8 :: X86Reg R.GP -> Location addr (BVType 8)
reg_high8 r = subRegister n8 n8 r

-- | The XMM part of a YMM register.
-- Setting does not affect the upper 128 bits (SSE compatability mode)
reg_low128_sse :: X86Reg R.YMM -> Location addr R.XMM
reg_low128_sse r = subRegister n0 n128 r

-- | The XMM part of a YMM register.
-- Setting clears the upper 128 bits (AVX mode)
reg_low128_avx :: X86Reg (BVType 256) -> Location addr (BVType 128)
reg_low128_avx r = constUpperBitsOnWriteRegister n128 ZeroExtendOnWrite r

reg_high128 :: X86Reg (BVType 256) -> Location addr (BVType 128)
reg_high128 r = subRegister n128 n128 r

rax, rcx, rdx, rbx, rsp, rbp, rsi, rdi :: Location addr (BVType 64)
rax = fullRegister R.RAX
rcx = fullRegister R.RCX
rdx = fullRegister R.RDX
rbx = fullRegister R.RBX
rsp = fullRegister R.RSP
rbp = fullRegister R.RBP
rsi = fullRegister R.RSI
rdi = fullRegister R.RDI

eax :: Location addr (BVType 32)
eax = reg_low32 R.RAX

ebx :: Location addr (BVType 32)
ebx = reg_low32 R.RBX

ecx :: Location addr (BVType 32)
ecx = reg_low32 R.RCX

edx :: Location addr (BVType 32)
edx = reg_low32 R.RDX

ax :: Location addr (BVType 16)
ax = reg_low16 R.RAX

bx :: Location addr (BVType 16)
bx = reg_low16 R.RBX

cx :: Location addr (BVType 16)
cx = reg_low16 R.RCX

dx :: Location addr (BVType 16)
dx = reg_low16 R.RDX

al :: Location addr (BVType 8)
al = reg_low8 R.RAX

dl :: Location addr (BVType 8)
dl = reg_low8 R.RDX

ah :: Location addr (BVType 8)
ah = reg_high8 R.RAX

rip :: Location addr (BVType 64)
rip = fullRegister R.X86_IP

-- | Access the low-order 256-bits in legacy SSE mode (upper 256-bits preserved)
ymm_preserve :: F.YMMReg -> Location addr (BVType 256)
ymm_preserve r = subRegister n0 n256 (R.ZMM (F.ymmRegNo r))

-- | Access the low-order 256-bits in legacy SSE mode (upper 256-bits zeroed)
ymm_zero :: F.YMMReg -> Location addr (BVType 256)
ymm_zero r = constUpperBitsOnWriteRegister n256 ZeroExtendOnWrite (R.ZMM (F.ymmRegNo r))

xmm_sse :: F.XMMReg -> Location addr (BVType 128)
xmm_sse r = subRegister n0 n128 (R.ZMM (F.xmmRegNo r))

xmm_avx :: F.XMMReg -> Location addr (BVType 128)
xmm_avx r = constUpperBitsOnWriteRegister n128 ZeroExtendOnWrite (R.ZMM (F.xmmRegNo r))

xmmOwner :: F.XMMReg -> X86Reg (BVType 512)
xmmOwner r = R.ZMM (F.xmmRegNo r)

------------------------------------------------------------------------

packWord :: forall st ids n
         . 1 <= n
         => R.BitPacking n
         -> X86Generator st ids (BVExpr ids n)
packWord (R.BitPacking sz bits) = do
  let getMoveBits :: R.BitConversion n -> X86Generator st ids (Expr ids (BVType n))
      getMoveBits (R.ConstantBit b off) =
        return $ bvLit sz (if b then 1 `Bits.shiftL` widthVal off else (0 :: Integer))
      getMoveBits (R.RegisterBit reg off) = do
        v <- uext sz <$> get (fullRegister reg)
        return $ v `bvShl` bvLit sz (intValue off)
  injs <- mapM getMoveBits bits
  return (foldl1 (.|.) injs)

unpackWord :: forall st ids n
           . (1 <= n)
           => R.BitPacking n
           -> BVExpr ids n
           -> X86Generator st ids ()
unpackWord (R.BitPacking sz bits) v = mapM_ unpackOne bits
  where
    unpackOne :: R.BitConversion n -> X86Generator st ids ()
    unpackOne R.ConstantBit{}         = return ()
    unpackOne (R.RegisterBit reg off) = do
      let res_w = typeWidth reg
      fullRegister reg .= bvTrunc res_w (v `bvShr` bvLit sz (intValue off))

------------------------------------------------------------------------
-- Values

-- | Choose a value based upon the boolean (basically a pure if then else)
mux :: Expr ids BoolType -> Expr ids tp -> Expr ids tp -> Expr ids tp
mux c x y
  | Just True  <- asBoolLit c = x
  | Just False <- asBoolLit c = y
  | x == y = x
  | Just (NotApp cn) <- asApp c = mux cn y x
  | otherwise = app $ Mux (typeRepr x) c x y

-- | Construct a literal bit vector.  The result is undefined if the
-- literal does not fit withint the given number of bits.
bvLit :: 1 <= n => NatRepr n -> Integer -> Expr ids (BVType n)
bvLit n v = ValueExpr $ mkLit n v

-- | Add two bitvectors together dropping overflow.
(.+) :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .+ y
  -- Eliminate add 0
  | Just 0 <- asUnsignedBVLit y = x
  | Just 0 <- asUnsignedBVLit x = y

  -- Constant folding.
  | ValueExpr (BVValue w xv) <- x
  , ValueExpr (BVValue _ yv) <- y
  = bvLit w (xv + yv)

  | ValueExpr (RelocatableValue w a) <- x
  , ValueExpr (BVValue _ o) <- y
  = ValueExpr (RelocatableValue w (a & incAddr (fromInteger o)))

  | ValueExpr (RelocatableValue w a) <- y
  , ValueExpr (BVValue _ o) <- x

  = ValueExpr (RelocatableValue w (a & incAddr (fromInteger o)))

  -- Shift constants to right-hand-side.
  | ValueExpr (BVValue _ _) <- x = y .+ x

  | otherwise = app $ BVAdd (typeWidth x) x y

-- | Subtract two vectors, ignoring underflow.
(.-) :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .- y = app $ BVSub (typeWidth x) x y

-- | Performs a multiplication of two bitvector values.
(.*) :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .* y
  | Just 0 <- asUnsignedBVLit x = x
  | Just 1 <- asUnsignedBVLit x = y
  | Just 0 <- asUnsignedBVLit y = y
  | Just 1 <- asUnsignedBVLit y = x

  | Just xv <- asUnsignedBVLit x, Just yv <- asUnsignedBVLit y =
      bvLit (typeWidth x) (xv * yv)
  | otherwise = app $ BVMul (typeWidth x) x y

-- | 2's complement
bvNeg :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n)
bvNeg n = bvLit (typeWidth n) 0 .- n

-- | Bitwise complement
bvComplement :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n)
bvComplement x
  | Just xv <- asUnsignedBVLit x = bvLit (typeWidth x) (Bits.complement xv)
    -- not (not p) = p
  | Just (BVComplement _ y) <- asApp x = y
  | otherwise = app $ BVComplement (typeWidth x) x

-- | Bitwise and
(.&.) :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .&. y
  | Just xv <- asUnsignedBVLit x, Just yv <- asUnsignedBVLit y =
      bvLit (typeWidth x) (xv Bits..&. yv)
  -- Eliminate and when one argument is maxUnsigned
  | Just xv <- asUnsignedBVLit x, xv == maxUnsigned (typeWidth x) = y
  | Just yv <- asUnsignedBVLit y, yv == maxUnsigned (typeWidth x) = x
  -- Cancel when and with 0.
  | Just 0 <- asUnsignedBVLit x = x
  | Just 0 <- asUnsignedBVLit y = y
  -- Idempotence
  | x == y = x

  -- Make literal the second argument (simplifies later cases)
  | isJust (asUnsignedBVLit x) = assert (isNothing (asUnsignedBVLit y)) $ y .&. x

  --(x1 .&. x2) .&. y = x1 .&. (x2 .&. y) -- Only apply when x2 and y is a lit
  | isJust (asUnsignedBVLit y)
  , Just (BVAnd _ x1 x2) <- asApp x
  , isJust (asUnsignedBVLit x2) =
    x1 .&. (x2 .&. y)

  -- (x1 .|. x2) .&. y = (x1 .&. y) .|. (x2 .&. y) -- Only apply when y and x2 is a lit.
  | isJust (asUnsignedBVLit y)
  , Just (BVOr _ x1 x2) <- asApp x
  ,  isJust (asUnsignedBVLit x2) =
      (x1 .&. y) .|. (x2 .&. y)
  -- x .&. (y1 .|. y2) = (y1 .&. x) .|. (y2 .&. x) -- Only apply when x and y2 is a lit.
  | isJust (asUnsignedBVLit x)
  , Just (BVOr _ y1 y2) <- asApp y
  , isJust (asUnsignedBVLit y2) =
      (y1 .&. x) .|. (y2 .&. x)

  -- Default case
  | otherwise = app $ BVAnd (typeWidth x) x y

-- | Bitwise or
(.|.) :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .|. y
  | Just xv <- asUnsignedBVLit x, Just yv <- asUnsignedBVLit y =
      bvLit (typeWidth x) (xv Bits..|. yv)
  -- Cancel or when one argument is maxUnsigned
  | Just xv <- asUnsignedBVLit x, xv == maxUnsigned (typeWidth x) = x
  | Just yv <- asUnsignedBVLit y, yv == maxUnsigned (typeWidth x) = y
  -- Eliminate "or" when one argument is 0
  | Just 0 <- asUnsignedBVLit x = y
  | Just 0 <- asUnsignedBVLit y = x
  -- Idempotence
  | x == y = x
  -- Default case
  | otherwise = app $ BVOr (typeWidth x) x y

-- | Exclusive or
bvXor :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvXor x y
  -- Eliminate xor with 0.
  | Just 0 <- asUnsignedBVLit x = y
  | Just 0 <- asUnsignedBVLit y = x
  -- Eliminate xor with self.
  | x == y = bvLit (typeWidth x) (0::Integer)
  -- If this is a single bit comparison with a constant, resolve to Boolean operation.
  | ValueExpr (BVValue w v) <- y
  , Just Refl <- testEquality w n1 =
      if v /= 0 then bvComplement x else x
  -- Default case.
  | otherwise = app $ BVXor (typeWidth x) x y

-- | Equality
(.=.) :: Expr ids tp -> Expr ids tp -> Expr ids BoolType
x .=. y
  | x == y = true
  -- Statically resolve two literals
  | ValueExpr (BVValue _ xv) <- x
  , ValueExpr (BVValue _ yv) <- y =
      boolValue (xv == yv)
  -- Move constant to second argument (We implicitly know both x and y
  -- are not a constant due to previous case).
  | ValueExpr BVValue{} <- x  = y .=. x
  | ValueExpr (BoolValue True)  <- x = y
  | ValueExpr (BoolValue False) <- x = boolNot y
  | ValueExpr (BoolValue True)  <- y = x
  | ValueExpr (BoolValue False) <- y = boolNot x

    -- Rewrite (u-v) .=. 0 to @u .=. v@.
  | ValueExpr (BVValue _ 0) <- y
  , Just (BVSub _ u v) <- asApp x =
      u .=. v

  -- General case
  | otherwise = app $ Eq x y

-- | Inequality
(.=/=.) :: Expr ids tp -> Expr ids tp -> Expr ids BoolType
bv .=/=. bv' = boolNot (bv .=. bv')

-- | Return true if value is zero.
is_zero :: (1 <= n) => Expr ids (BVType n) -> Expr ids BoolType
is_zero x = x .=. bvLit (typeWidth x) (0::Integer)

-- | Concatentates two bit vectors.
--
-- Big-endian, so higher-order bits come from first argument.
bvCat :: forall ids m n
      . (1 <= m, 1 <= n)
      => Expr ids (BVType m) -> Expr ids (BVType n) -> Expr ids (BVType (m + n))
bvCat h l =
    case _1_le_m_plus_n of
      LeqProof -> go
  where
      -- GHC 7.10 has a context stack overflow related to @1 <= m + n@
      -- which goes away when we factor the body out like this.
      go :: (1 <= m + n) => Expr ids (BVType (m + n))
      go =
        case ( m_le_m_plus_n , n_le_m_plus_n , _1_le_m_plus_n ) of
          (LeqProof, LeqProof, LeqProof) ->
            let highOrderBits =
                  uext m_plus_n h `bvShl` bvLit m_plus_n (intValue $ n)
                lowOrderBits = uext m_plus_n l
            in highOrderBits .|. lowOrderBits

      m :: NatRepr m
      m = typeWidth h

      n :: NatRepr n
      n = typeWidth l

      m_plus_n :: NatRepr (m + n)
      m_plus_n = addNat m n

      m_le_m_plus_n :: LeqProof m (m + n)
      m_le_m_plus_n = addIsLeq m n

      n_le_m_plus_n :: LeqProof n (m + n)
      n_le_m_plus_n = addPrefixIsLeq m n

      _1_le_m_plus_n :: LeqProof 1 (m + n)
      _1_le_m_plus_n =
        leqAdd (LeqProof :: LeqProof 1 m) n

-- | Splits a bit vectors into two.
--
-- Big-endian, so higher-order bits make up first component of
-- result.
bvSplit :: forall ids n . (1 <= n) => Expr ids (BVType (n + n)) -> (Expr ids (BVType n), Expr ids (BVType n))
bvSplit v =
  let sz = halfNat (typeWidth v) :: NatRepr n
   in case leqAdd (LeqProof :: LeqProof 1 n) sz :: LeqProof 1 (n + n) of
        LeqProof ->
          case leqAdd (leqRefl sz) sz :: LeqProof n (n + n) of
            LeqProof ->
              let sh = bvLit (typeWidth v) (intValue sz)
               in (bvTrunc sz (v `bvShr` sh), bvTrunc sz v)

-- | Vectorization
bvVectorize :: forall ids k n
               . (1 <= k, 1 <= n)
              => NatRepr k
              -> Expr ids (BVType n)
              -> [Expr ids (BVType k)]
bvVectorize sz bv
  | Just Refl <- testEquality (typeWidth bv) sz = [bv]
  | Just LeqProof <- testLeq sz (typeWidth bv) =
       let bvs2n :: [Expr ids (BVType (k+k))] -- solve for size (n+n), then split into size n
           bvs2n = withLeqProof (dblPosIsPos (LeqProof :: LeqProof 1 k)) $
              bvVectorize (addNat sz sz) bv
        in concatMap (\v -> let (a, b) = bvSplit v in [a, b]) bvs2n
bvVectorize _ _ = error "Unhandled case"

-- | Given a list of values this concatenates them together
bvUnvectorize :: forall ids k n. (1 <= k) => NatRepr n -> [Expr ids (BVType k)] -> Expr ids (BVType n)
bvUnvectorize sz [x]
  | Just Refl <- testEquality (typeWidth x) sz = x
bvUnvectorize sz bvs = withLeqProof (dblPosIsPos (LeqProof :: LeqProof 1 k)) $
      bvUnvectorize sz $ concatBVPairs bvs
    where concatBVPairs :: (1 <= o) => [Expr ids (BVType o)] -> [Expr ids (BVType (o+o))]
          concatBVPairs (x:y:zs) = (x `bvCat` y) : concatBVPairs zs
          concatBVPairs _ = []

vectorize2 :: (1 <= k, 1 <= n)
           => NatRepr k
           -> (Expr ids (BVType k) -> Expr ids (BVType k) -> Expr ids (BVType k))
           -> Expr ids (BVType n) -> Expr ids (BVType n)
           -> Expr ids (BVType n)
vectorize2 sz f x y = let xs = bvVectorize sz x
                          ys = bvVectorize sz y
                       in bvUnvectorize (typeWidth x) $ zipWith f xs ys

-- | Rotations
bvRol :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvRol v n = bvShl v n .|. bvShr v bits_less_n
  where bits_less_n = bvLit (typeWidth v) (intValue $ typeWidth v) .- n

bvRor :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvRor v n = bvShr v n .|. bvShl v bits_less_n
  where bits_less_n = bvLit (typeWidth v) (intValue $ typeWidth v) .- n

-- | Shifts, the semantics is undefined for shifts >= the width of the first argument.
--
-- The first argument is the value to shift, and the second argument
-- is the number of bits to shift by.
bvShr :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvShr x y
  | Just 0 <- asUnsignedBVLit y = x
  | Just 0 <- asUnsignedBVLit x = x
  | otherwise = app $ BVShr (typeWidth x) x y

bvSar :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvSar x y = app $ BVSar (typeWidth x) x y

bvShl :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvShl x y
    | Just 0 <- asUnsignedBVLit y = x

    | Just xv <- asUnsignedBVLit x
    , Just yv <- asUnsignedBVLit y =
      assert (yv <= toInteger (maxBound :: Int)) $
        bvLit (typeWidth x) (xv `Bits.shiftL` fromInteger yv)

      -- Replace "(x >> c) << c" with (x .&. - 2^c)
    | Just yv <- asUnsignedBVLit y
    , Just (BVShr w x_base (asUnsignedBVLit -> Just x_shft)) <- asApp x
    , x_shft == yv =
      x_base .&. bvLit w (negate (2^x_shft) ::Integer)

    | Just yv <- asUnsignedBVLit y
    , yv >= intValue (typeWidth x) =
        bvLit (typeWidth x) (0 :: Integer)

    | otherwise = app $ BVShl (typeWidth x) x y


-- | Version of 'bvTrunc' that precludes trivial truncations; see
-- 'uext'' docs.
bvTrunc' :: (1 <= m, m+1 <= n) => NatRepr m -> Expr ids (BVType n) -> Expr ids (BVType m)
bvTrunc' w e0
  | Just v <- asUnsignedBVLit e0 =
      bvLit w v
  | Just Refl <- testEquality (typeWidth e0) w =
      e0
  | Just (MMXExtend e) <- asArchFn e0
  , Just Refl <- testEquality w n64 =
      ValueExpr e
  | Just (UExt e _) <- asApp e0 =
      case testLeq w (typeWidth e) of
        -- Check if original value width is less than new width.
        Just LeqProof -> bvTrunc w e
        Nothing ->
          -- Runtime check to wordaround GHC typechecker
          case testLeq (typeWidth e) w of
            Just LeqProof -> uext w e
            Nothing -> error "bvTrunc internal error"
        -- Trunc (x .&. y) w = trunc x w .&. trunc y w
  | Just (BVAnd _ x y) <- asApp e0 =
      let x' = bvTrunc' w x
          y' = bvTrunc' w y
       in x' .&. y'
      -- Trunc (x .|. y) w = trunc x w .|. trunc y w
  | Just (BVOr _ x y) <- asApp e0 =
      let x' = bvTrunc' w x
          y' = bvTrunc' w y
       in x' .|. y'
      -- trunc (Trunc e w1) w2 = trunc e w2
  | Just (Trunc e _) <- asApp e0 =
      -- Runtime check to workaround GHC typechecker.
      case testLeq w (typeWidth e) of
        Just LeqProof -> bvTrunc w e
        Nothing -> error "bvTrunc given bad width"
      -- Default case
  | otherwise = app (Trunc e0 w)

-- | Truncate the value.
--
-- Returns 'm' lower order bits.
bvTrunc :: (1 <= m, m <= n) => NatRepr m -> Expr ids (BVType n) -> Expr ids (BVType m)
bvTrunc w e =
  case testStrictLeq w (typeWidth e) of
    Left LeqProof -> bvTrunc' w e
    Right Refl -> e

-- | Unsigned less than
bvUlt :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvUlt x y
  | Just xv <- asUnsignedBVLit x, Just yv <- asUnsignedBVLit y = boolValue (xv < yv)
  | x == y = false
    -- Simplify @xlit < uext y w@ to @xlit < y@ or @False@ depending on literal constant.
  | Just xc <- asUnsignedBVLit x
  , Just (UExt ysub _) <- asApp y
  , wsub <- typeWidth ysub =
      -- If constant is greater than max value then this is just false.
      if xc >= maxUnsigned wsub then
        ValueExpr (BoolValue False)
       else
         app $ BVUnsignedLt (ValueExpr (BVValue wsub xc)) ysub
  | otherwise =  app $ BVUnsignedLt x y

-- | Unsigned less than or equal.
bvUle :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvUle x y
  | Just xv <- asUnsignedBVLit x, Just yv <- asUnsignedBVLit y = boolValue (xv <= yv)
  | x == y = true
  | otherwise = app $ BVUnsignedLe x y

-- | Signed less than
bvSlt :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvSlt x y
  | Just xv <- asSignedBVLit x, Just yv <- asSignedBVLit y = boolValue (xv < yv)
  | x == y = false
  | otherwise = app $ BVSignedLt x y

-- | Returns bit at index given by second argument, 0 being lsb
-- If the bit index is greater than or equal to n, then the result is zero.
bvBit :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvBit x y
  | Just xv <- asUnsignedBVLit x
  , Just yv <- asUnsignedBVLit y =
      boolValue (xv `Bits.testBit` fromInteger yv)
  | Just (Trunc xe w) <- asApp x
  , Just LeqProof <- testLeq n1 (typeWidth xe)
  , Just yv <- asUnsignedBVLit y = assert (0 <= yv && yv < intValue w) $
    bvBit xe (ValueExpr (BVValue (typeWidth xe) yv))

  | otherwise =
      app $ BVTestBit x y

-- | Return most significant bit of number.
msb :: (1 <= n) => Expr ids (BVType n) -> Expr ids BoolType
msb v = bvSlt v (bvLit (typeWidth v) (0::Integer))
  -- FIXME: should be log2 (typeWidth v) here

-- | Version of 'sext' that precludes trivial extensions; see
-- 'uext'' docs.
sext' :: (1 <= m, m+1 <= n, 1 <= n) => NatRepr n -> Expr ids (BVType m) -> Expr ids (BVType n)
sext' w e0
  -- Collapse duplicate extensions.
  | Just (SExt e w0) <- asApp e0 = do
      let we = typeWidth e
      withLeqProof (leqTrans (ltProof we w0) (ltProof w0 w)) $
        sext w e
  | otherwise = app (SExt e0 w)

-- | Perform a signed extension of a bitvector.
sext :: forall ids m n . (1 <= m, m <= n) => NatRepr n -> Expr ids (BVType m) -> Expr ids (BVType n)
sext w e =
  case ( testStrictLeq (typeWidth e) w
       , leqTrans (LeqProof :: LeqProof 1 m) (LeqProof :: LeqProof m n)
       ) of
    (Left LeqProof, LeqProof) -> sext' w e
    (Right Refl,_) -> e

-- | Perform a unsigned extension of a bitvector.
--
-- Unlike 'uext' below, this is a strict extension: the 'm+1 <= n' means 'm < n'.
--
-- We have this strict version because constructors which reify
-- these ops, e.g. @App@ in Reopt and Crucible, are strict in this
-- sense.
uext' :: (1 <= m, m+1 <= n, 1 <= n) => NatRepr n -> Expr ids (BVType m) -> Expr ids (BVType n)
uext' w e0
  -- Literal case
  | Just v <- asUnsignedBVLit e0 =
    let w0 = typeWidth e0
     in withLeqProof (leqTrans (leqProof n1 w0) (ltProof w0 w)) $
        bvLit w v
  -- Collapse duplicate extensions.
  | Just (UExt e w0) <- asApp e0 = do
      let we = typeWidth e
      withLeqProof (leqTrans (ltProof we w0) (ltProof w0 w)) $
        uext w e

  -- Default case
  | otherwise = app (UExt e0 w)

-- | Perform a unsigned extension of a bitvector.
uext :: forall ids m n
     . (1 <= m, m <= n)
     => NatRepr n
     -> Expr ids (BVType m)
     -> Expr ids (BVType n)
uext w e =
  case ( testStrictLeq (typeWidth e) w
       , leqTrans (LeqProof :: LeqProof 1 m) (LeqProof :: LeqProof m n)
       ) of
    (Left LeqProof, LeqProof) -> uext' w e
    (Right Refl,_) -> e

-- | Return least-significant nibble (4 bits).
least_nibble :: forall ids n . (4 <= n) => Expr ids (BVType n) -> Expr ids (BVType 4)
least_nibble = bvTrunc knownNat

-- | Return least-significant byte.
least_byte :: forall ids n . (8 <= n) => Expr ids (BVType n) -> Expr ids (BVType 8)
least_byte = bvTrunc knownNat

-- | Return true expression if a signed add-with carry would overflow.
-- This holds if the sign bits of the arguments are the same, and the sign
-- of the result is different.
sadc_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType -> Expr ids BoolType
sadc_overflows x y c
  | Just 0 <- asUnsignedBVLit y, Just False <- asBoolLit c = false
  | otherwise = app $ SadcOverflows x y c

-- | Return true expression is signed add overflows.  See
-- @sadc_overflows@ for definition.
sadd_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
sadd_overflows x y = sadc_overflows x y false

-- | Return true expression if a unsigned add-with carry would overflow.
uadc_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType -> Expr ids BoolType
uadc_overflows x y c
  | Just 0 <- asUnsignedBVLit y, Just False <- asBoolLit c = false
  | otherwise = app $ UadcOverflows x y c

-- | Return true expression is unsigned add overflows.  See
-- @sadc_overflows@ for definition.
uadd_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
uadd_overflows x y = uadc_overflows x y false

-- | Return true expression if unsigned sbb overflows.
-- @usbb_overflows x y c@ is true when @x - (y+c)@ with
-- x,y interpreted as unsigned numbers and c a borrow bit,
-- would return a negative result.
usbb_overflows :: (1 <= n)
                 => Expr ids (BVType n)
                 -> Expr ids (BVType n)
                 -> Expr ids BoolType
                 -> Expr ids BoolType
usbb_overflows x y c
  | Just 0 <- asUnsignedBVLit y, Just False <- asBoolLit c = false
    -- If the borrow bit is zero, this is equivalent to unsigned x < y.
  | Just False <- asBoolLit c = bvUlt x y
  | otherwise = app $ UsbbOverflows x y c

-- | Return true expression if unsigned sub overflows.
-- @usub_overflows x y@ is true when @x - y@ (interpreted as unsigned numbers),
-- would return a negative result.
usub_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
usub_overflows x y = usbb_overflows x y false

-- | Return true expression if unsigned sub overflows.
-- @ssbb_overflows x y c@ is true when @x - (y+c)@ with
-- x,y interpreted as signed numbers and c a borrow bit,
-- would return a number different from the expected integer due to
-- wrap-around.
ssbb_overflows :: (1 <= n)
                 => Expr ids (BVType n)
                 -> Expr ids (BVType n)
                 -> Expr ids BoolType
                 -> Expr ids BoolType
ssbb_overflows x y c
  | Just 0 <- asUnsignedBVLit y, Just False <- asBoolLit c = false
    -- If the borrow bit is zero, this is equivalent to signed x < y.
    -- FIXME: not true? | Just 0 <- asUnsignedBVLit c = app $ BVSignedLt x y
  | otherwise = app $ SsbbOverflows x y c

-- | Return true expression is signed sub overflows.
ssub_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
ssub_overflows x y = ssbb_overflows x y false

-- | bsf "bit scan forward" returns the index of the least-significant
-- bit that is 1.  Undefined if value is zero.
-- All bits at indices less than return value must be unset.
bsf :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n)
bsf x = app $ Bsf (typeWidth x) x

-- | bsr "bit scan reverse" returns the index of the most-significant
-- bit that is 1.  Undefined if value is zero.
-- All bits at indices greater than return value must be unset.
bsr :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n)
bsr x = app $ Bsr (typeWidth x) x

boolValue :: Bool -> Expr ids BoolType
boolValue = ValueExpr . BoolValue

true :: Expr ids BoolType
true = boolValue True

false :: Expr ids BoolType
false = boolValue False

boolNot :: Expr ids BoolType -> Expr ids BoolType
boolNot x
  | Just xv <- asBoolLit x = boolValue (not xv)
    -- not (not p) = p
  | Just (NotApp y) <- asApp x = y
  | Just (BVUnsignedLe u v) <- asApp x = AppExpr (BVUnsignedLt v u)
  | Just (BVUnsignedLt u v) <- asApp x = AppExpr (BVUnsignedLe v u)
  | Just (BVSignedLe u v) <- asApp x = AppExpr (BVSignedLt v u)
  | Just (BVSignedLt u v) <- asApp x = AppExpr (BVSignedLe v u)
  | otherwise = app $ NotApp x

(.&&.) :: Expr ids BoolType -> Expr ids BoolType -> Expr ids BoolType
x .&&. y
  | Just True  <- asBoolLit x = y
  | Just False <- asBoolLit x = x
  | Just True  <- asBoolLit y = x
  | Just False <- asBoolLit y = y
  -- Idempotence
  | x == y = x

  -- x1 <= x2 & x1 ~= x2 = x1 < x2
  | Just (BVUnsignedLe x1 x2) <- asApp x
  , Just (NotApp yc) <- asApp y
  , Just (Eq y1 y2) <- asApp yc
  , BVTypeRepr w <- typeRepr y1
  , Just Refl <- testEquality (typeWidth x1) w
  , (x1,x2) == (y1,y2) || (x1,x2) == (y2,y1) =
    bvUlt x1 x2

  -- x1 ~= x2 & x1 <= x2 => x1 < x2
  | Just (BVUnsignedLe y1 y2) <- asApp y
  , Just (NotApp xc) <- asApp x
  , Just (Eq x1 x2) <- asApp xc
  , BVTypeRepr w <- typeRepr x1
  , Just Refl <- testEquality w (typeWidth y1)
  , (x1,x2) == (y1,y2) || (x1,x2) == (y2,y1) =
    bvUlt y1 y2
  -- Default case
  | otherwise = app $ AndApp x y

(.||.) :: Expr ids BoolType -> Expr ids BoolType -> Expr ids BoolType
x .||. y
  | Just True  <- asBoolLit x = x
  | Just False <- asBoolLit x = y
  | Just True  <- asBoolLit y = y
  | Just False <- asBoolLit y = x
     -- Idempotence
  | x == y = x
    -- Rewrite "x < y | x == y" to "x <= y"
  | Just (BVUnsignedLt x1 x2) <- asApp x
  , Just (Eq y1 y2) <- asApp y
  , BVTypeRepr w <- typeRepr y1
  , Just Refl <- testEquality (typeWidth x1) w
  , (x1,x2) == (y1,y2) || (x1,x2) == (y2,y1)
  = bvUle x1 x2
    -- Default case
  | otherwise = app $ OrApp x y

boolXor :: Expr ids BoolType -> Expr ids BoolType -> Expr ids BoolType
boolXor x y
  -- Eliminate xor with 0.
  | Just False <- asBoolLit x = y
  | Just True  <- asBoolLit x = boolNot y
  | Just False <- asBoolLit y = x
  | Just True  <- asBoolLit y = boolNot x
  -- Eliminate xor with self.
  | x == y = false
  -- If this is a single bit comparison with a constant, resolve to Boolean operation.
  -- Default case.
  | otherwise = app $ XorApp x y

-- | Construct a literal bit vector.  The result is undefined if the
-- literal does not fit withint the given number of bits.
bvKLit :: (KnownNat n, 1 <= n) => Integer -> Expr ids (BVType n)
bvKLit = bvLit knownNat

infixl 7 .*
infixl 6 .+
infixl 6 .-
infix  4 .=

------------------------------------------------------------------------
-- Semantics

-- | Defines operations that need to be supported at a specific bitwidth.
type SupportedBVWidth n
   = ( 1 <= n
     , 4 <= n
     , 8 <= n
     , KnownNat n
     )

repValHasSupportedWidth :: RepValSize w -> (SupportedBVWidth w => a) -> a
repValHasSupportedWidth rval x =
  case rval of
    ByteRepVal  -> x
    WordRepVal  -> x
    DWordRepVal -> x
    QWordRepVal -> x

-- | Create a fresh "undefined" value.
make_undefined :: TypeRepr tp -> X86Generator st ids (Expr ids tp)
make_undefined tp =
  evalAssignRhs (SetUndefined tp)

type Addr s = Expr s (BVType 64)

-- | Mark a Boolean variable as undefined.
set_undefined :: KnownRepr TypeRepr tp => Location (Addr ids) tp -> X86Generator st ids ()
set_undefined l = do
  u <- make_undefined knownRepr
  l .= u

-- | Read from the given location.
get :: forall st ids tp . Location (Addr ids) tp -> X86Generator st ids (Expr ids tp)
get l0 =
  case l0 of
    MemoryAddr w tp -> do
      addr <- eval w
      evalAssignRhs (ReadMem addr tp)
    FullRegister r -> getReg r
    Register rv -> do
      registerViewRead rv <$> getReg (registerViewReg rv)
    -- TODO
    X87StackRegister i -> do
      idx <- getX87Offset i
      getReg (X87_FPUReg (F.mmxReg (fromIntegral idx)))


-- | Assign a value to a location.
(.=) :: Location (Addr ids) tp -> Expr ids tp -> X86Generator st ids ()
l .= e = setLoc l =<< eval e

-- | Modify the value at a location
modify :: Location (Addr ids) tp
       -> (Expr ids tp -> Expr ids tp)
       -> X86Generator st ids ()
modify r f = do
  x <- get r
  r .= f x

-- | Return true if value contains an even number of true bits.
even_parity :: BVExpr ids 8 -> X86Generator st ids (Expr ids BoolType)
even_parity v = do
  val_v <- eval v
  evalArchFn (EvenParity val_v)

-- FIXME: those should also mutate the underflow/overflow flag and
-- related state.

-- | X87 support --- these both affect the register stack for the
-- x87 state.
x87Push :: Expr ids (FloatBVType X86_80Float) -> X86Generator st ids ()
x87Push e = do
  v <- eval e
  topv <- getX87Top
  let new_top = fromIntegral $ (topv - 1) Bits..&. 0x7
  -- TODO: Update tagWords
  -- Store value at new top
  setReg (X87_FPUReg (F.mmxReg new_top)) v
  -- Update top
  setReg X87_TopReg (BVValue knownNat (toInteger new_top))

x87Pop :: X86Generator st ids ()
x87Pop = do
  topv <- getX87Top
  let new_top = (topv + 1) Bits..&. 0x7
  -- Update top
  setReg X87_TopReg (BVValue knownNat (toInteger new_top))

type BVExpr ids w = Expr ids (BVType w)
