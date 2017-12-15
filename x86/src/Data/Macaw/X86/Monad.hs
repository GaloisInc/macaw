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
  , floatMemRepr
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

  , mkFPAddr
  , packWord
  , unpackWord
  -- ** Registers
  , rip
  , rax, rbx, rcx, rdx, rsp, rbp, rsi, rdi
  , eax, ebx, ecx, edx
  , ax, bx, cx, dx
  , al, dl
  , ah
  , ymm
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
  , ifte_
  , when_
  , unless_
  , memcopy
  , memcmp
  , memset
  , even_parity
  , fnstcw
  , getSegmentBase
  , exception
  , ExceptionClass(..)
  , x87Push
  , x87Pop
  , bvQuotRem
  , bvSignedQuotRem

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
import           Data.Macaw.CFG.Block
import           Data.Macaw.Memory (Endianness(..))
import           Data.Macaw.Types
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import qualified Data.Sequence as Seq
import qualified Flexdis86 as F
import           Flexdis86.Segment ( Segment )
import           Flexdis86.Sizes (SizeConstraint(..))
import           GHC.TypeLits as TypeLits
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))


import           Data.Macaw.X86.ArchTypes
import           Data.Macaw.X86.Generator
import           Data.Macaw.X86.X86Reg (X86Reg(..))
import qualified Data.Macaw.X86.X86Reg as R
import           Data.Macaw.X86.X87ControlReg

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
    bvTrunc n $ v0 `bvShr` bvLit (typeWidth v0) (natValue b)

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
      myMask = maxUnsigned n `Bits.shiftL` fromInteger (natValue b)
      -- Generate max for old bits.
      notMyMask = Bits.complement myMask
      prevBits = v0 .&. bvLit w notMyMask
      w = typeWidth v0
      cl = typeWidth rn
      b' = natValue b
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
  -- A location in the virtual address space of the process.
  MemoryAddr :: !addr -> !(MemRepr tp) -> Location addr tp

  FullRegister :: !(X86Reg tp)
               -> Location addr tp

  Register :: !(RegisterView m b n)
           -> Location addr (BVType n)

  ControlReg :: !F.ControlReg
             -> Location addr (BVType 64)

  DebugReg :: !F.DebugReg
           -> Location addr (BVType 64)

  SegmentReg :: !Segment
             -> Location addr (BVType 16)

  X87ControlReg :: !(X87_ControlReg w)
                -> Location addr (BVType w)

  -- The register stack: the argument is an offset from the stack
  -- top, so X87Register 0 is the top, X87Register 1 is the second,
  -- and so forth.
  X87StackRegister :: !Int
                   -> Location addr (FloatType X86_80Float)

------------------------------------------------------------------------
-- Location

-- | Type for addresses.
type AddrExpr ids = Expr ids (BVType 64)

type ImpLocation ids tp = Location (AddrExpr ids) tp

readLoc :: X86PrimLoc tp -> X86Generator st_s ids (Expr ids tp)
readLoc l = evalArchFn (ReadLoc l)

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


addWriteLoc :: X86PrimLoc tp -> Value X86_64 ids tp -> X86Generator st_s ids ()
addWriteLoc l v = addArchStmt $ WriteLoc l v

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

   ControlReg r -> do
     addWriteLoc (ControlLoc r) v
   DebugReg r  ->
     addWriteLoc (DebugLoc r) v

   SegmentReg s
     | s == F.FS -> addWriteLoc FS v
     | s == F.GS -> addWriteLoc GS v
       -- Otherwise registers are 0.
     | otherwise ->
       fail $ "On x86-64 registers other than fs and gs may not be set."

   X87ControlReg r ->
     addWriteLoc (X87_ControlLoc r) v
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
ppLocation :: forall addr tp. (addr -> Doc) -> Location addr tp -> Doc
ppLocation ppAddr loc = case loc of
  MemoryAddr addr _tr -> ppAddr addr
  Register rv -> ppReg rv
  FullRegister r -> text $ "%" ++ show r
  ControlReg r -> text (show r)
  DebugReg r -> text (show r)
  SegmentReg r -> text (show r)
  X87ControlReg r -> text ("x87_" ++ show r)
  X87StackRegister i -> text $ "x87_stack@" ++ show i
  where
    -- | Print subrange as Python-style slice @<location>[<low>:<high>]@.
    --
    -- The low bit is inclusive and the high bit is exclusive, but I
    -- can't bring myself to generate @<reg>[<low>:<high>)@ :)
    ppReg :: RegisterView w n cl -> Doc
    ppReg rv =
      text $ "%" ++ show (_registerViewReg rv) ++
        if b == 0 && s == (fromIntegral $ natValue (typeWidth $ _registerViewReg rv))
        then ""
        else "[" ++ show b ++ ":" ++ show s ++ "]"
      where
        b = natValue $ _registerViewBase rv
        s = natValue $ _registerViewSize rv

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
  typeRepr (ControlReg _)    = knownRepr
  typeRepr (DebugReg _)    = knownRepr
  typeRepr (SegmentReg _)    = knownRepr
  typeRepr (X87ControlReg r) =
    case x87ControlRegWidthIsPos r of
      LeqProof -> BVTypeRepr (typeRepr r)
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

-- | Maps float info repr to associated MemRepr.
floatMemRepr :: FloatInfoRepr flt -> MemRepr (FloatType flt)
floatMemRepr fir =
  case floatInfoBytesIsPos fir of
    LeqProof -> BVMemRepr (floatInfoBytes fir) LittleEndian

-- | Tuen an address into a location of size @n
mkFPAddr :: FloatInfoRepr flt -> addr -> Location addr (FloatType flt)
mkFPAddr fir addr = MemoryAddr addr (floatMemRepr fir)

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
reg_low128_avx :: X86Reg R.YMM -> Location addr R.XMM
reg_low128_avx r = constUpperBitsOnWriteRegister n128 ZeroExtendOnWrite r

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

ymm :: F.YMMReg -> Location addr (BVType 256)
ymm = fullRegister . R.YMM

xmm_sse :: F.XMMReg -> Location addr (BVType 128)
xmm_sse = reg_low128_sse . xmmOwner

xmm_avx :: F.XMMReg -> Location addr (BVType 128)
xmm_avx = reg_low128_avx . xmmOwner

xmmOwner :: F.XMMReg -> X86Reg (BVType 256)
xmmOwner = R.YMM . F.ymmReg . F.xmmRegNo

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
        return $ v `bvShl` bvLit sz (natValue off)
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
      fullRegister reg .= bvTrunc res_w (v `bvShr` bvLit sz (natValue off))

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
bvLit n v = ValueExpr $ mkLit n (toInteger v)

-- | Add two bitvectors together dropping overflow.
(.+) :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .+ y
  -- Eliminate add 0
  | Just 0 <- asBVLit y = x
  | Just 0 <- asBVLit x = y

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

  -- Reorganize addition by constant to offset.
  | Just (BVAdd w x_base (asBVLit -> Just x_off)) <- asApp x
  , ValueExpr (BVValue _ y_off) <- y
  = x_base .+ bvLit w (x_off + y_off)

  | Just (BVAdd w y_base (asBVLit -> Just y_off)) <- asApp y
  , ValueExpr (BVValue _ x_off) <- x
  = y_base .+ bvLit w (x_off + y_off)

  | otherwise = app $ BVAdd (typeWidth x) x y

-- | Subtract two vectors, ignoring underflow.
(.-) :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .- y
  | ValueExpr (BVValue _ yv) <- y =
      x .+ bvLit (typeWidth x) (negate yv)
  | otherwise = app $ BVSub (typeWidth x) x y

-- | Performs a multiplication of two bitvector values.
(.*) :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .* y
  | Just 0 <- asBVLit x = x
  | Just 1 <- asBVLit x = y
  | Just 0 <- asBVLit y = y
  | Just 1 <- asBVLit y = x

  | Just xv <- asBVLit x, Just yv <- asBVLit y =
      bvLit (typeWidth x) (xv * yv)
  | otherwise = app $ BVMul (typeWidth x) x y

-- | 2's complement
bvNeg :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n)
bvNeg n = bvLit (typeWidth n) 0 .- n

-- | Bitwise complement
bvComplement :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n)
bvComplement x
  | Just xv <- asBVLit x = bvLit (typeWidth x) (Bits.complement xv)
    -- not (not p) = p
  | Just (BVComplement _ y) <- asApp x = y
  | otherwise = app $ BVComplement (typeWidth x) x

-- | Bitwise and
(.&.) :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .&. y
  | Just xv <- asBVLit x, Just yv <- asBVLit y =
      bvLit (typeWidth x) (xv Bits..&. yv)
  -- Eliminate and when one argument is maxUnsigned
  | Just xv <- asBVLit x, xv == maxUnsigned (typeWidth x) = y
  | Just yv <- asBVLit y, yv == maxUnsigned (typeWidth x) = x
  -- Cancel when and with 0.
  | Just 0 <- asBVLit x = x
  | Just 0 <- asBVLit y = y
  -- Idempotence
  | x == y = x

  -- Make literal the second argument (simplifies later cases)
  | isJust (asBVLit x) = assert (isNothing (asBVLit y)) $ y .&. x

  --(x1 .&. x2) .&. y = x1 .&. (x2 .&. y) -- Only apply when x2 and y is a lit
  | isJust (asBVLit y)
  , Just (BVAnd _ x1 x2) <- asApp x
  , isJust (asBVLit x2) =
    x1 .&. (x2 .&. y)

  -- (x1 .|. x2) .&. y = (x1 .&. y) .|. (x2 .&. y) -- Only apply when y and x2 is a lit.
  | isJust (asBVLit y)
  , Just (BVOr _ x1 x2) <- asApp x
  ,  isJust (asBVLit x2) =
      (x1 .&. y) .|. (x2 .&. y)
  -- x .&. (y1 .|. y2) = (y1 .&. x) .|. (y2 .&. x) -- Only apply when x and y2 is a lit.
  | isJust (asBVLit x)
  , Just (BVOr _ y1 y2) <- asApp y
  , isJust (asBVLit y2) =
      (y1 .&. x) .|. (y2 .&. x)

  -- Default case
  | otherwise = app $ BVAnd (typeWidth x) x y

-- | Bitwise or
(.|.) :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
x .|. y
  | Just xv <- asBVLit x, Just yv <- asBVLit y =
      bvLit (typeWidth x) (xv Bits..|. yv)
  -- Cancel or when one argument is maxUnsigned
  | Just xv <- asBVLit x, xv == maxUnsigned (typeWidth x) = x
  | Just yv <- asBVLit y, yv == maxUnsigned (typeWidth x) = y
  -- Eliminate "or" when one argument is 0
  | Just 0 <- asBVLit x = y
  | Just 0 <- asBVLit y = x
  -- Idempotence
  | x == y = x
  -- Default case
  | otherwise = app $ BVOr (typeWidth x) x y

-- | Exclusive or
bvXor :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvXor x y
  -- Eliminate xor with 0.
  | Just 0 <- asBVLit x = y
  | Just 0 <- asBVLit y = x
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
  -- Move constant to second argument (We implicitly know both x and y are not a constant due to previous case).
  | ValueExpr BVValue{} <- x  = y .=. x

  -- Rewrite "base + offset = constant" to "base = constant - offset".
  | Just (BVAdd w x_base (asBVLit -> Just x_off)) <- asApp x
  , ValueExpr (BVValue _ yv) <- y =
      app $ Eq x_base (bvLit w (yv - x_off))
      -- Rewrite "u - v == c" to "u = c + v".
  | Just (BVSub _ x_1 x_2) <- asApp x = x_1 .=. (y .+ x_2)
  -- Rewrite "c == u - v" to "u = c + v".
  | Just (BVSub _ y_1 y_2) <- asApp y = y_1 .=. (x .+ y_2)

  | ValueExpr (BoolValue True)  <- x = y
  | ValueExpr (BoolValue False) <- x = boolNot y
  | ValueExpr (BoolValue True)  <- y = x
  | ValueExpr (BoolValue False) <- y = boolNot x

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
                  uext m_plus_n h `bvShl` bvLit m_plus_n (natValue $ n)
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
              let sh = bvLit (typeWidth v) (natValue sz)
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
  where bits_less_n = bvLit (typeWidth v) (natValue $ typeWidth v) .- n

bvRor :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvRor v n = bvShr v n .|. bvShl v bits_less_n
  where bits_less_n = bvLit (typeWidth v) (natValue $ typeWidth v) .- n

-- | Shifts, the semantics is undefined for shifts >= the width of the first argument.
--
-- The first argument is the value to shift, and the second argument
-- is the number of bits to shift by.
--
-- Big-endian, so left shift moves bits to higher-order positions
-- and right shift moves bits to lower-order positions.
bvShr :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvShr x y
  | Just 0 <- asBVLit y = x
  | Just 0 <- asBVLit x = x
  | otherwise = app $ BVShr (typeWidth x) x y

bvSar :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvSar x y = app $ BVSar (typeWidth x) x y

bvShl :: 1 <= n => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids (BVType n)
bvShl x y
    | Just 0 <- asBVLit y = x

    | Just xv <- asBVLit x
    , Just yv <- asBVLit y =
      assert (yv <= toInteger (maxBound :: Int)) $
        bvLit (typeWidth x) (xv `Bits.shiftL` fromInteger yv)

      -- Replace "(x >> c) << c" with (x .&. - 2^c)
    | Just yv <- asBVLit y
    , Just (BVShr w x_base (asBVLit -> Just x_shft)) <- asApp x
    , x_shft == yv =
      x_base .&. bvLit w (negate (2^x_shft) ::Integer)

    | Just yv <- asBVLit y
    , yv >= natValue (typeWidth x) = bvLit (typeWidth x) (0 :: Integer)

    | otherwise = app $ BVShl (typeWidth x) x y


-- | Version of 'bvTrunc' that precludes trivial truncations; see
-- 'uext'' docs.
bvTrunc' :: (1 <= m, m+1 <= n) => NatRepr m -> Expr ids (BVType n) -> Expr ids (BVType m)
bvTrunc' w e0
  | Just v <- asBVLit e0 =
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
bvUlt :: Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvUlt x y
  | Just xv <- asBVLit x, Just yv <- asBVLit y = boolValue (xv < yv)
  | x == y = false
  | otherwise =
      case typeRepr x of
        BVTypeRepr _ -> app $ BVUnsignedLt x y

-- | Unsigned less than or equal.
bvUle :: Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvUle x y = boolNot (bvUlt y x)

-- | Signed less than
bvSlt :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvSlt x y
  | Just xv <- asBVLit x, Just yv <- asBVLit y = boolValue (xv < yv)
  | x == y = false
  | otherwise =
      case typeRepr x of
        BVTypeRepr _ -> app $ BVSignedLt x y

-- | Returns bit at index given by second argument, 0 being lsb
-- If the bit index is greater than or equal to n, then the result is zero.
bvBit :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvBit x y
  | Just xv <- asBVLit x
  , Just yv <- asBVLit y =
      boolValue (xv `Bits.testBit` fromInteger yv)
  | Just (Trunc xe w) <- asApp x
  , Just LeqProof <- testLeq n1 (typeWidth xe)
  , Just yv <- asBVLit y = assert (0 <= yv && yv < natValue w) $
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
  | Just v <- asBVLit e0 =
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
  | Just 0 <- asBVLit y, Just False <- asBoolLit c = false
  | otherwise = app $ SadcOverflows x y c

-- | Return true expression is signed add overflows.  See
-- @sadc_overflows@ for definition.
sadd_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
sadd_overflows x y = sadc_overflows x y false

-- | Return true expression if a unsigned add-with carry would overflow.
uadc_overflows :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType -> Expr ids BoolType
uadc_overflows x y c
  | Just 0 <- asBVLit y, Just False <- asBoolLit c = false
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
  | Just 0 <- asBVLit y, Just False <- asBoolLit c = false
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
  | Just 0 <- asBVLit y, Just False <- asBoolLit c = false
    -- If the borrow bit is zero, this is equivalent to signed x < y.
    -- FIXME: not true? | Just 0 <- asBVLit c = app $ BVSignedLt x y
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
false = boolValue True

boolNot :: Expr ids BoolType -> Expr ids BoolType
boolNot x
  | Just xv <- asBoolLit x = boolValue (not xv)
    -- not (y < z) = y >= z = z <= y
  | Just (BVUnsignedLt y z) <- asApp x = bvUle z y
    -- not (y <= z) = y > z = z < y
  | Just (BVUnsignedLe y z) <- asApp x = bvUlt z y
    -- not (y < z) = y >= z = z <= y
  | Just (BVSignedLt y z) <- asApp x = bvSle z y
    -- not (y <= z) = y > z = z < y
  | Just (BVSignedLe y z) <- asApp x = bvSlt z y
    -- not (not p) = p
  | Just (NotApp y) <- asApp x = y
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
  , ((x1,x2) == (y1,y2) || (x1,x2) == (y2,y1)) =
      bvUlt x1 x2

  -- x1 ~= x2 & x1 <= x2 => x1 < x2
  | Just (BVUnsignedLe y1 y2) <- asApp y
  , Just (NotApp xc) <- asApp x
  , Just (Eq x1 x2) <- asApp xc
  , BVTypeRepr w <- typeRepr x1
  , Just Refl <- testEquality w (typeWidth y1)
  , ((x1,x2) == (y1,y2) || (x1,x2) == (y2,y1)) =
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

bvSle :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvSle x y = app (BVSignedLe x y)

-- | Construct a literal bit vector.  The result is undefined if the
-- literal does not fit withint the given number of bits.
bvKLit :: (KnownNat n, 1 <= n) => Integer -> Expr ids (BVType n)
bvKLit = bvLit knownNat

infixl 7 .*
infixl 6 .+
infixl 6 .-
infix  4 .=

------------------------------------------------------------------------
-- Monadic definition
data ExceptionClass
   = DivideError -- #DE
   | FloatingPointError
   | SIMDFloatingPointException
   | GeneralProtectionException Int
   | UndefinedInstructionError -- basically for ud2
     -- ^ A general protection exception with the given error code.
     -- -- | AlignmentCheck
  deriving (Eq, Ord, Show)

------------------------------------------------------------------------
-- Semantics

-- | Defines operations that need to be supported at a specific bitwidht.
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
    ControlReg _ ->
      fail $ "Do not support reading control registers."
    DebugReg _ ->
      fail $ "Do not support reading debug registers."
    SegmentReg s
      | s == F.FS -> readLoc FS
      | s == F.GS -> readLoc GS
        -- Otherwise registers are 0.
      | otherwise ->
        fail $ "On x86-64 registers other than fs and gs may not be read."
    X87ControlReg r ->
      readLoc (X87_ControlLoc r)
    FullRegister r -> getReg r
    Register rv -> do
      registerViewRead rv <$> getReg (registerViewReg rv)
    -- TODO
    X87StackRegister i -> do
      idx <- getX87Offset i
      getReg (X87_FPUReg (F.mmxReg (fromIntegral idx)))


-- | Assign a value to alocation.
(.=) :: Location (Addr ids) tp -> Expr ids tp -> X86Generator st ids ()
l .= e = setLoc l =<< eval e

-- | Modify the value at a location
modify :: Location (Addr ids) tp
       -> (Expr ids tp -> Expr ids tp)
       -> X86Generator st ids ()
modify r f = do
  x <- get r
  r .= f x

 -- | Perform an if-then-else
ifte_ :: Expr ids BoolType
      -> X86Generator st ids ()
      -> X86Generator st ids ()
      -> X86Generator st ids ()
-- Implement ifte_
-- Note that this implementation will run any code appearing after the ifte_
-- twice, once for the true branch and once for the false branch.
--
-- This could be changed to run the code afterwards once, but the cost would be
-- defining a way to merge processor states from the different branches, and making
-- sure that expression assignments generated in one branch were not referred to in
-- another branch.
--
-- One potential design change, not implemented here, would be to run both branches,
-- up to the point where they merge, and if the resulting PC is in the same location,
-- to merge in that case, otherwise to run them separately.
--
-- This would support the cmov instruction, but result in divergence for branches, which
-- I think is what we want.
ifte_ c_expr t f = eval c_expr >>= go
    where
      go (BoolValue True) = t
      go (BoolValue False) = f
      go cond =
        shiftX86GCont $ \c s0 -> do
          let p_b = s0 ^.blockState
          let st = p_b^.pBlockState
          let t_block_label = s0^.blockSeq^.nextBlockID
          let s2 = s0 & blockSeq . nextBlockID +~ 1
                      & blockSeq . frontierBlocks .~ Seq.empty
                      & blockState .~ emptyPreBlock st t_block_label (genAddr s0)
          -- Run true block.
          t_seq <- finishBlock FetchAndExecute <$> runX86Generator c s2 t
          -- Run false block
          let f_block_label = t_seq^.nextBlockID
          let s5 = GenState { assignIdGen = assignIdGen s0
                            , _blockSeq =
                                BlockSeq { _nextBlockID    = t_seq^.nextBlockID + 1
                                         , _frontierBlocks = Seq.empty
                                         }
                            , _blockState = emptyPreBlock st f_block_label (genAddr s0)
                            , genAddr = genAddr s0
                            , genMemory = genMemory s0
                            , avxMode = avxMode s0
                            }
          f_seq <- finishBlock FetchAndExecute <$> runX86Generator c s5 f

          -- Join results together.
          let fin_b = finishBlock' p_b (\_ -> Branch cond t_block_label f_block_label)
          seq fin_b $ do
          return $
            GenResult { resBlockSeq =
                         BlockSeq { _nextBlockID = _nextBlockID f_seq
                                  , _frontierBlocks = (s0^.blockSeq^.frontierBlocks Seq.|> fin_b)
                                               Seq.>< t_seq^.frontierBlocks
                                               Seq.>< f_seq^.frontierBlocks
                                  }
                      , resState = Nothing
                      }

-- | Run a step if condition holds.
when_ :: Expr ids BoolType -> X86Generator st ids () -> X86Generator st ids ()
when_ p x = ifte_ p x (return ())

-- | Run a step if condition is false.
unless_ :: Expr ids BoolType -> X86Generator st ids () -> X86Generator st ids ()
unless_ p = ifte_ p (return ())

-- | Move n bits at a time, with count moves
--
-- Semantic sketch. The effect on memory should be like @memcopy@
-- below, not like @memcopy2@. These sketches ignore the issue of
-- copying in chunks of size `bytes`, which should only be an
-- efficiency concern.
--
-- @
-- void memcopy(int bytes, int copies, char *src, char *dst, int reversed) {
--   int maybeFlip = reversed ? -1 : 1;
--   for (int c = 0; c < copies; ++c) {
--     for (int b = 0; b < bytes; ++b) {
--       int offset = maybeFlip * (b + c * bytes);
--       *(dst + offset) = *(src + offset);
--     }
--   }
-- }
-- @
--
-- Compare with:
--
-- @
-- void memcopy2(int bytes, int copies, char *src, char *dst, int reversed) {
--   int maybeFlip = reversed ? -1 : 1;
--   /* The only difference from `memcopy` above: here the same memory is
--      copied whether `reversed` is true or false -- only the order of
--      copies changes -- whereas above different memory is copied for
--      each direction. */
--   if (reversed) {
--     /* Start at the end and work backwards. */
--     src += copies * bytes - 1;
--     dst += copies * bytes - 1;
--   }
--   for (int c = 0; c < copies; ++c) {
--     for (int b = 0; b < bytes; ++b) {
--       int offset = maybeFlip * (b + c * bytes);
--       *(dst + offset) = *(src + offset);
--     }
--   }
-- }
-- @
memcopy :: Integer
           -- ^ Number of bytes to copy at a time (1,2,4,8)
        -> BVExpr ids 64
           -- ^ Number of values to move.
        -> Addr ids
           -- ^ Start of source buffer
        -> Addr ids
           -- ^ Start of destination buffer.
        -> Expr ids BoolType
           -- ^ Flag indicates direction of move:
           -- True means we should decrement buffer pointers after each copy.
           -- False means we should increment the buffer pointers after each copy.
        -> X86Generator st ids ()
memcopy val_sz count src dest is_reverse = do
  count_v <- eval count
  src_v   <- eval src
  dest_v  <- eval dest
  is_reverse_v <- eval is_reverse
  addArchStmt $ MemCopy val_sz count_v src_v dest_v is_reverse_v

-- | Compare the memory regions.  Returns the number of elements which are
-- identical.  If the direction is 0 then it is increasing, otherwise decreasing.
--
-- See `memcopy` above for explanation of which memory regions are
-- compared: the regions copied there are compared here.
memcmp :: Integer
          -- ^ Number of bytes to compare at a time {1, 2, 4, 8}
       -> BVExpr ids 64
          -- ^ Number of elementes to compare
       -> Addr ids
          -- ^ Pointer to first buffer
       -> Addr ids
          -- ^ Pointer to second buffer
       -> Expr ids BoolType
          -- ^ Flag indicates direction of copy:
          -- True means we should decrement buffer pointers after each copy.
           -- False means we should increment the buffer pointers after each copy.
       -> X86Generator st ids (BVExpr ids 64)
memcmp sz count src dest is_reverse = do
  count_v <- eval count
  is_reverse_v <- eval is_reverse
  src_v   <- eval src
  dest_v  <- eval dest
  evalArchFn (MemCmp sz count_v src_v dest_v is_reverse_v)

-- | Set memory to the given value, for the number of words (nbytes
-- = count * typeWidth v)
memset :: (1 <= n)
       => BVExpr ids 64
          -- ^ Number of values to set
       -> BVExpr ids n
          -- ^ Value to set
       -> Addr ids
          -- ^ Pointer to buffer to set
       -> Expr ids BoolType
          -- ^ Direction flag
       -> X86Generator st ids ()
memset count val dest dfl = do
  count_v <- eval count
  val_v   <- eval val
  dest_v  <- eval dest
  df_v    <- eval dfl
  addArchStmt $ MemSet count_v val_v dest_v df_v

-- | Return true if value contains an even number of true bits.
even_parity :: BVExpr ids 8 -> X86Generator st ids (Expr ids BoolType)
even_parity v = do
  val_v <- eval v
  evalArchFn (EvenParity val_v)

-- | Store floating point control word in given address.
fnstcw :: Addr ids -> X86Generator st ids ()
fnstcw addr = do
  addArchStmt =<< StoreX87Control <$> eval addr

-- | Return the base address of the given segment.
getSegmentBase :: Segment -> X86Generator st ids (Addr ids)
getSegmentBase seg =
  case seg of
    F.FS -> evalArchFn ReadFSBase
    F.GS -> evalArchFn ReadGSBase
    _ ->
      error $ "X86_64 getSegmentBase " ++ show seg ++ ": unimplemented!"

-- | raises an exception if the predicate is true and the mask is false
exception :: Expr ids BoolType    -- mask
          -> Expr ids BoolType -- predicate
          -> ExceptionClass
          -> X86Generator st ids ()
exception m p c =
  when_ (boolNot m .&&. p)
        (addStmt (PlaceHolderStmt [] $ "Exception " ++ (show c)))

-- FIXME: those should also mutate the underflow/overflow flag and
-- related state.

-- | X87 support --- these both affect the register stack for the
-- x87 state.
x87Push :: Expr ids (FloatType X86_80Float) -> X86Generator st ids ()
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

-- | Unsigned division.
--
-- The x86 documentation for @div@ (Intel x86 manual volume 2A,
-- page 3-393) says that results should be truncated towards
-- zero. These operations are called @quot@ and @rem@ in Haskell,
-- whereas @div@ and @mod@ in Haskell round towards negative
-- infinity.
--
-- This should raise a #DE exception if the denominator is zero or the
-- result is larger than maxUnsigned n.
bvQuotRem :: (1 <= w)
          => RepValSize w
          -> Expr ids (BVType (w+w))
          -- ^ Numerator
          -> Expr ids (BVType w)
             -- ^ Denominator
          -> X86Generator st_s ids (BVExpr ids w, BVExpr ids w)
bvQuotRem rep n d = do
  nv <- eval n
  dv <- eval d
  (,) <$> evalArchFn (X86Div rep nv dv)
      <*> evalArchFn (X86Rem rep nv dv)

-- | Signed division.
--
-- The x86 documentation for @idiv@ (Intel x86 manual volume 2A, page
-- 3-393) says that results should be truncated towards zero. These
-- operations are called @quot@ and @rem@ in Haskell, whereas @div@
-- and @mod@ in Haskell round towards negative infinity.
--
-- This should raise a #DE exception if the denominator is zero or the
-- result is larger than maxSigned n or less than minSigned n.
bvSignedQuotRem :: (1 <= w)
                => RepValSize w
                -> BVExpr ids (w+w)
                   -- ^ Numerator
                -> BVExpr ids w
                   -- ^ Denominator
                -> X86Generator st_s ids (BVExpr ids w, BVExpr ids w)
bvSignedQuotRem rep n d = do
  nv <- eval n
  dv <- eval d
  (,) <$> evalArchFn (X86IDiv rep nv dv)
      <*> evalArchFn (X86IRem rep nv dv)
