{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module provides definitions for x86 instructions.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NondecreasingIndentation #-}
module Data.Macaw.X86.Semantics
  ( execInstruction
  ) where

import           Control.Lens ((^.))
import           Control.Monad (when)
import qualified Data.Bits as Bits
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import           Data.Parameterized.Classes
import qualified Data.Parameterized.List as P
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Proxy
import           Data.Word
import qualified Flexdis86 as F

import           Data.Macaw.CFG ( MemRepr(..)
                                , memReprBytes
                                , App(..)
                                , Value(BoolValue, AssignedValue)
                                , AssignRhs(CondReadMem, ReadMem)
                                , mkLit
                                )
import           Data.Macaw.Memory (Endianness (LittleEndian))
import           Data.Macaw.Types


import           Data.Macaw.X86.ArchTypes
import           Data.Macaw.X86.Generator
import           Data.Macaw.X86.Getters
import           Data.Macaw.X86.InstructionDef
import           Data.Macaw.X86.Monad
import           Data.Macaw.X86.X86Reg (X86Reg)
import qualified Data.Macaw.X86.X86Reg as R
import qualified Data.Macaw.X86.Semantics.AVX as AVX

type Addr s = Expr s (BVType 64)
type BVExpr ids w = Expr ids (BVType w)

-- * Preliminaries

-- The representation for a address
addrRepr :: MemRepr (BVType 64)
addrRepr = BVMemRepr n8 LittleEndian

type Binop
  = forall st ids n
  .   SupportedBVWidth n
  => Location (Expr ids (BVType 64)) (BVType n)
  -> Expr ids (BVType n)
  -> X86Generator st ids ()

uadd4_overflows :: 4 <= n
                => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
uadd4_overflows x y = uadd_overflows (least_nibble x) (least_nibble y)

usub4_overflows :: 4 <= n
                => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
usub4_overflows x y = usub_overflows (least_nibble x) (least_nibble y)

uadc4_overflows :: 4 <= n
                => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType -> Expr ids BoolType
uadc4_overflows x y c = uadc_overflows (least_nibble x) (least_nibble y) c

fmap_loc :: Location (Addr ids) (BVType n)
         -> (BVExpr ids n -> BVExpr ids n)
         -> X86Generator st ids ()
fmap_loc l f = do
  lv <- get l
  l .= f lv

-- | Update flags with given result value.
set_result_flags :: SupportedBVWidth n => Expr ids (BVType n) -> X86Generator st ids ()
set_result_flags res = do
  sf_loc .= msb res
  zf_loc .= is_zero res
  (pf_loc .=) =<< even_parity (least_byte res)

-- | Assign value to location and update corresponding flags.
set_result_value :: SupportedBVWidth n
                 => Location (Addr ids) (BVType n)
                 -> BVExpr ids n
                 -> X86Generator st ids ()
set_result_value dst res = do
  set_result_flags res
  dst .= res

-- | Set bitwise flags.
set_bitwise_flags :: SupportedBVWidth n => BVExpr ids n -> X86Generator st ids ()
set_bitwise_flags res = do
  of_loc .= false
  cf_loc .= false
  set_undefined af_loc
  set_result_flags res

push :: MemRepr tp -> Expr ids tp -> X86Generator st ids ()
push repr v = do
  old_sp <- get rsp
  let delta   = bvLit n64 $ memReprBytes repr -- delta in bytes
      new_sp  = old_sp .- delta
  MemoryAddr new_sp repr .= v
  rsp     .= new_sp

pop :: MemRepr tp -> X86Generator st ids (Expr ids tp)
pop repr = do
  -- Get current stack pointer value.
  old_sp <- get rsp
  -- Get value at stack pointer.
  v   <- get (MemoryAddr old_sp repr)
  -- Increment stack pointer
  rsp .= old_sp .+ bvLit n64 (memReprBytes repr)
  -- Return value
  return v

readBV32 :: Addr ids -> X86Generator st ids (BVExpr ids 32)
readBV32 addr = get (MemoryAddr addr dwordMemRepr)

readBV64 :: Addr ids -> X86Generator st ids (BVExpr ids 64)
readBV64 addr = get (MemoryAddr addr qwordMemRepr)

-- | Read a 32 or 64-bit register or meory value
getRM32_RM64 :: F.Value
             -> X86Generator st ids (Either (Location (Addr ids) (BVType 32)) (Location (Addr ids) (BVType 64)))
getRM32_RM64 v =
  case v of
    F.DWordReg r -> pure $ Left  $ reg32Loc r
    F.QWordReg r -> pure $ Right $ reg64Loc r
    F.Mem32 addr -> Left  <$> getBV32Addr addr
    F.Mem64 addr -> Right <$> getBV64Addr addr
    _ -> fail "Unexpected operand"

-- | The the low bits in a register.
setLowBits :: forall st_s ids l w
           .  (1 <= l, l <= w, KnownNat l, KnownNat w)
           => X86Reg (BVType w)
           -> Expr ids (BVType l)
           -> X86Generator st_s ids ()
setLowBits r e = do
  let w :: NatRepr w
      w = knownNat
  let l :: NatRepr l
      l = knownNat
  -- Get initial value
  v0 <- getReg r
  -- Get old bits
  LeqProof <- pure $ leqTrans (LeqProof @1 @l) (LeqProof @l @w)
  let prevBits = v0 .&. bvLit w (Bits.complement (maxUnsigned l))
  -- Or prevBits with new value
  v1 <- eval $ prevBits .|. uext w e
  setReg r v1

-- | Location that get the low 32 bits of a XMM register,
-- and preserves the high 64 bits on writes.
xmm_low32 :: F.XMMReg -> Location addr (BVType 32)
xmm_low32 r = subRegister n0 n32 (xmmOwner r)

-- | Location that get the low 64 bits of a YMM register,
-- and preserves the high 64 bits on writes.
xmm_low64 :: F.XMMReg -> Location addr (BVType 64)
xmm_low64 r = subRegister n0 n64 (xmmOwner r)

-- | Location that get the low 64 bits of a XMM register,
-- and preserves the high 64 bits on writes.
xmm_low :: F.XMMReg -> SSE_FloatType tp -> Location addr (FloatBVType tp)
xmm_low r SSE_Single = xmm_low32 r
xmm_low r SSE_Double = xmm_low64 r

-- | Location that get the high 64 bits of a XMM register,
-- and preserves the low 64 bits on writes.
xmm_high64 :: F.XMMReg -> Location addr (BVType 64)
xmm_high64 r = subRegister n64 n64 (xmmOwner r)

singleMemRepr :: MemRepr (FloatType SingleFloat)
singleMemRepr = FloatMemRepr SingleFloatRepr

doubleMemRepr :: MemRepr (FloatType DoubleFloat)
doubleMemRepr = FloatMemRepr DoubleFloatRepr

xmmSingleMemRepr :: MemRepr (VecType 4 (FloatType SingleFloat))
xmmSingleMemRepr = PackedVecMemRepr n4 singleMemRepr

readMem :: F.AddrRef -> MemRepr tp -> X86Generator st ids (Value X86_64 ids tp)
readMem addrRef repr = do
  addr <- eval =<< getBVAddress addrRef
  AssignedValue <$> addAssignment (ReadMem addr repr)

getXMMreg_float_low :: F.XMMReg -> SSE_FloatType tp -> X86Generator st ids (Value X86_64 ids (FloatType tp))
getXMMreg_float_low r SSE_Single =
  eval . bitcast knownRepr . bvTrunc' n32 =<< getReg (xmmOwner r)
getXMMreg_float_low r SSE_Double =
  eval . bitcast knownRepr . bvTrunc' n64 =<< getReg (xmmOwner r)

-- | This gets the value of a xmm/m128 field as 4 floats
getXMMreg_sv :: F.XMMReg -> X86Generator st ids (Value X86_64 ids (VecType 4 (FloatType SingleFloat)))
getXMMreg_sv r = eval . bitcast knownRepr . bvTrunc' n128 =<< getReg (xmmOwner r)

-- | This gets the value of a xmm/m128 field as 4 floats
getXMM_sv :: F.Value -> X86Generator st ids (Value X86_64 ids (VecType 4 (FloatType SingleFloat)))
getXMM_sv (F.XMMReg r) = getXMMreg_sv r
getXMM_sv (F.Mem128 addrRef) = readMem addrRef xmmSingleMemRepr
getXMM_sv _ = fail "Unexpected argument"

-- | This gets the value of a xmm/m128 field as 4 floats
setXMMreg_sv :: F.XMMReg -> Expr ids (VecType 4 (FloatType SingleFloat)) -> X86Generator st ids ()
setXMMreg_sv r e = setLowBits (xmmOwner r) (bitcast (BVTypeRepr n128) e)

-- | This gets the value of a xmm/m64 field.
--
-- If it is an XMM value, it gets the low 64bit register.
-- If it is a memory address is gets the 64bits there.
-- Otherwise it fails.
getXMM_float_low :: F.Value -> SSE_FloatType tp -> X86Generator st ids (Value X86_64 ids (FloatType tp))
getXMM_float_low (F.XMMReg r) tp = getXMMreg_float_low r tp
getXMM_float_low (F.Mem128 addrRef) SSE_Single = readMem addrRef singleMemRepr
getXMM_float_low (F.Mem128 addrRef) SSE_Double = readMem addrRef doubleMemRepr
getXMM_float_low _ _ = fail "Unexpected argument"

-- | The the least significant float or double in an XMM register
setXMMreg_float_low :: F.XMMReg -> SSE_FloatType tp -> Expr ids (FloatType tp) -> X86Generator st ids ()
setXMMreg_float_low r SSE_Single e = do
  setLowBits (xmmOwner r) (bitcast (BVTypeRepr n32) e)
setXMMreg_float_low r SSE_Double e = do
  setLowBits (xmmOwner r) (bitcast (BVTypeRepr n64) e)

-- ** Condition codes

-- * General Purpose Instructions
-- ** Data Transfer Instructions

-- FIXME: has the side effect of reading r, but this should be safe because r can only be a register.

def_cmov_list :: [InstructionDef]
def_cmov_list =
  defConditionals "cmov" $ \mnem cc ->
    defBinaryLV mnem $ \r y -> do
      c <- cc
      r_v <- get r
      r .= mux c y r_v

def_bswap :: InstructionDef
def_bswap = defUnary "bswap" $ \_ val -> do
  SomeBV l <- getSomeBVLocation val
  v0 <- get l
  l .= (bvUnvectorize (typeWidth l) $ reverse $ bvVectorize n8 v0)

def_xadd :: InstructionDef
def_xadd =
  defBinaryLL "xadd" $ \_ d s -> do
    d0 <- get d
    s0 <- get s
    s .= d0
    exec_add d s0 -- sets flags

-- | Sign extend al -> ax, ax -> eax, eax -> rax, resp.
def_cbw :: InstructionDef
def_cbw = defNullary "cbw" $ do
  v <- get al
  ax .= sext n16 v

def_cwde :: InstructionDef
def_cwde = defNullary "cwde" $ do
  v <- get ax
  eax .= sext n32 v

def_cdqe :: InstructionDef
def_cdqe = defNullary "cdqe" $ do
  v <- get eax
  rax .= sext n64 v

def_pop :: InstructionDef
def_pop =
  defUnary "pop" $ \_ fval -> do
    Some (HasRepSize rep l) <- getAddrRegOrSegment fval
    val <- pop (repValSizeMemRepr rep)
    l .= val

def_push :: InstructionDef
def_push =
  defUnary "push" $ \_ val -> do
    Some (HasRepSize rep v) <- getAddrRegSegmentOrImm val
    push (repValSizeMemRepr rep) v

-- | Sign extend ax -> dx:ax, eax -> edx:eax, rax -> rdx:rax, resp.
def_cwd :: InstructionDef
def_cwd = defNullary "cwd" $ do
  v <- get ax
  let (upper, lower) = bvSplit (sext n32 v)
  dx .= upper
  ax .= lower

def_cdq :: InstructionDef
def_cdq = defNullary "cdq" $ do
  v <- get eax
  let (upper, lower) = bvSplit (sext n64 v)
  edx .= upper
  eax .= lower

def_cqo :: InstructionDef
def_cqo = defNullary "cqo" $ do
  v <- get rax
  let (upper, lower) = bvSplit (sext knownNat v)
  rdx .= upper
  rax .= lower

-- FIXME: special segment stuff?
-- FIXME: CR and debug regs?
def_mov :: InstructionDef
def_mov =
  defBinary "mov" $ \_ loc val -> do
    case (loc, val) of
      (F.ByteReg r, F.ByteReg src) -> do
        v <- get $ reg8Loc  src
        reg8Loc r .= v
      (F.ByteReg r, F.ByteImm i) -> do
        reg8Loc r .= bvLit n8 (toInteger i)
      (F.ByteReg r, F.Mem8 src) -> do
        v <- get =<< getBV8Addr src
        reg8Loc r  .= v
      (F.Mem8 a, F.ByteReg src) -> do
        l <- getBV8Addr a
        v <- get $ reg8Loc  src
        l .= v
      (F.Mem8 a, F.ByteImm i) -> do
        l <- getBV8Addr a
        l .= bvLit n8 (toInteger i)

      (F.WordReg r, F.WordReg src) -> do
        v <- get $ reg16Loc src
        reg16Loc r .= v
      (F.WordReg r, F.WordSignedImm i) -> do
        reg16Loc r .= bvLit n16 (toInteger i)
      (F.WordReg r, F.WordImm i) -> do
        reg16Loc r .= bvLit n16 (toInteger i)
      (F.WordReg r, F.Mem16 src) -> do
        v <- get =<< getBV16Addr src
        reg16Loc r .= v
      (F.Mem16 a, F.WordReg src) -> do
        l <- getBV16Addr a
        v <- get $ reg16Loc src
        l .= v
      (F.Mem16 a, F.WordSignedImm i) -> do
        l <- getBV16Addr a
        l .= bvLit n16 (toInteger i)

      (F.DWordReg r, F.DWordReg src) -> do
        v <- get $ reg32Loc src
        reg32Loc r .= v
      (F.DWordReg r, F.DWordSignedImm i) -> do
        reg32Loc r .= bvLit n32 (toInteger i)
      (F.DWordReg r, F.DWordImm i) -> do
        reg32Loc r .= getImm32 i
      (F.DWordReg r, F.Mem32 src) -> do
        v <- get =<< getBV32Addr src
        reg32Loc r .= v
      (F.Mem32 a, F.DWordReg src) -> do
        l <- getBV32Addr a
        v <- get $ reg32Loc src
        l .= v
      (F.Mem32 a, F.DWordSignedImm i) -> do
        l <- getBV32Addr a
        l .= bvLit n32 (toInteger i)

      (F.QWordReg r, F.QWordReg src) -> do
        v <- get $ reg64Loc src
        reg64Loc r .= v
      (F.QWordReg r, F.Mem64 src) -> do
        v <- get =<< getBV64Addr src
        reg64Loc r .= v
      (F.QWordReg r, F.QWordImm i) -> do
        reg64Loc r .= bvLit n64 (toInteger i)
      (F.QWordReg r, F.DWordSignedImm i) -> do
        reg64Loc r .= bvLit n64 (toInteger i)
      (F.Mem64 a, F.DWordSignedImm i) -> do
        l <- getBV64Addr a
        l .= bvLit n64 (toInteger i)
      (F.Mem64 a, F.QWordReg src) -> do
        l <- getBV64Addr a
        v <- get $ reg64Loc src
        l .= v

      (F.Mem16 a, F.SegmentValue s) -> do
        v <- get (SegmentReg s)
        l <- getBV16Addr  a
        l .= v
      (F.WordReg r, F.SegmentValue s) -> do
        v <- get (SegmentReg s)
        reg16Loc r .= v
      (F.DWordReg r, F.SegmentValue s) -> do
        v <- get (SegmentReg s)
        reg_low16 (R.X86_GP (F.reg32_reg r)) .= v
      (F.QWordReg r, F.SegmentValue s) -> do
        v <- get (SegmentReg s)
        fullRegister (R.X86_GP r) .= uext' n64 v

      (F.SegmentValue s, F.Mem16 a) -> do
        v <- get =<< getBV16Addr a
        SegmentReg s .= v
      (F.SegmentValue s, F.WordReg r) -> do
        v <- get (fullRegister (R.X86_GP (F.reg16_reg r)))
        SegmentReg s .= bvTrunc' n16 v
      (F.SegmentValue s, F.DWordReg r) -> do
        v <- get (fullRegister (R.X86_GP (F.reg32_reg r)))
        SegmentReg s .= bvTrunc' n16 v
      (F.SegmentValue s, F.QWordReg r) -> do
        v <- get (fullRegister (R.X86_GP r))
        SegmentReg s .= bvTrunc' n16 v

      (_, F.ControlReg _) -> do
        error "Do not support moving from/to control registers."
      (F.ControlReg _, _) -> do
        error "Do not support moving from/to control registers."
      (_, F.DebugReg _) -> do
        error "Do not support moving from/to debug registers."
      (F.DebugReg _, _) -> do
        error "Do not support moving from/to debug registers."

      _ -> do
        error $ "Unexpected arguments to mov: " ++ show loc ++ " " ++ show val

regLocation :: NatRepr n -> X86Reg (BVType 64) -> Location addr (BVType n)
regLocation sz
  | Just Refl <- testEquality sz n8  = reg_low8
  | Just Refl <- testEquality sz n16 = reg_low16
  | Just Refl <- testEquality sz n32 = reg_low32
  | Just Refl <- testEquality sz n64 = fullRegister
  | otherwise = fail "regLocation: Unknown bit width"

def_cmpxchg :: InstructionDef
def_cmpxchg  = defBinaryLV "cmpxchg" $ \d s -> do
  let acc = regLocation (typeWidth s) R.RAX
  temp <- get d
  a  <- get acc
  exec_cmp acc temp -- set flags
  let p = a .=. temp
  zf_loc .= p
  d .= mux p s temp
  modify acc $ mux p temp

def_cmpxchg8b :: InstructionDef
def_cmpxchg8b =
  defUnary "cmpxchg8b" $ \_ bloc -> do
    loc <-
      case bloc of
        F.Mem64 ar -> eval =<< getBVAddress ar
        F.VoidMem ar -> eval =<< getBVAddress ar
        _ -> fail "Unexpected argument to cmpxchg8b"
    eaxVal <- eval =<< get eax
    ebxVal <- eval =<< get ebx
    ecxVal <- eval =<< get ecx
    edxVal <- eval =<< get edx
    res <- evalArchFn (CMPXCHG8B loc eaxVal ebxVal ecxVal edxVal)
    zf_loc .= app (TupleField knownRepr res P.index0)
    eax    .= app (TupleField knownRepr res P.index1)
    edx    .= app (TupleField knownRepr res P.index2)

def_movsx :: InstructionDef
def_movsx = defBinaryLVge "movsx" $ \l v -> l .= sext (typeWidth l) v

def_movsxd :: InstructionDef
def_movsxd = defBinaryLVge "movsxd" $ \l v -> l .= sext (typeWidth l) v

def_movzx :: InstructionDef
def_movzx = defBinaryLVge "movzx" $ \l v -> do
  l .= uext (typeWidth l) v

-- The xchng instruction
def_xchg :: InstructionDef
def_xchg = defBinary "xchg" $ \_ f_loc f_loc' -> do
  SomeBV l <- getSomeBVLocation f_loc
  l' <- getBVLocation f_loc' (typeWidth l)
  v  <- get l
  v' <- get l'
  l  .= v'
  l' .= v

-- ** Binary Arithmetic Instructions

def_adc :: InstructionDef
def_adc = defBinaryLV "adc" $ \dst y -> do
  -- Get current value stored in destination.
  dst_val <- get dst
  -- Get current value of carry bit
  c <- get cf_loc
  -- Set overflow and arithmetic flags
  of_loc .= sadc_overflows  dst_val y c
  af_loc .= uadc4_overflows dst_val y c
  cf_loc .= uadc_overflows  dst_val y c
  -- Set result value.
  let w = typeWidth dst
  let cbv = mux c (bvLit w 1) (bvLit w 0)
  set_result_value dst (dst_val .+ y .+ cbv)

exec_add :: SupportedBVWidth n
         => Location (Addr ids) (BVType n)
         -> BVExpr ids n
         -> X86Generator st ids ()
exec_add dst y = do
  -- Get current value stored in destination.
  dst_val <- get dst
  -- Set overflow and arithmetic flags
  of_loc .= sadd_overflows  dst_val y
  af_loc .= uadd4_overflows dst_val y
  cf_loc .= uadd_overflows  dst_val y
  -- Set result value.
  set_result_value dst (dst_val .+ y)

-- FIXME: we don't need a location, just a value.
exec_cmp :: SupportedBVWidth n => Location (Addr ids) (BVType n) -> BVExpr ids n -> X86Generator st ids ()
exec_cmp dst y = do
  dst_val <- get dst
  -- Set overflow and arithmetic flags
  of_loc .= ssub_overflows  dst_val y
  af_loc .= usub4_overflows dst_val y
  cf_loc .= usub_overflows  dst_val y
  -- Set result value.
  set_result_flags (dst_val .- y)

def_dec :: InstructionDef
def_dec = defUnary  "dec" $ \_ dstVal -> do
  SomeBV dst <- getSomeBVLocation dstVal
  dst_val <- get dst
  let v1 = bvLit (typeWidth dst_val) 1
  -- Set overflow and arithmetic flags
  of_loc .= ssub_overflows  dst_val v1
  af_loc .= usub4_overflows dst_val v1
  -- no carry flag
  -- Set result value.
  set_result_value dst (dst_val .- v1)

set_div_flags :: X86Generator st ids ()
set_div_flags = do
  set_undefined cf_loc
  set_undefined of_loc
  set_undefined sf_loc
  set_undefined af_loc
  set_undefined pf_loc
  set_undefined zf_loc

-- | Helper function for @div@ and @idiv@ instructions.
--
-- The difference between @div@ and @idiv@ is whether the primitive
-- operations are signed or not.
--
-- The x86 division instructions are peculiar. A @2n@-bit numerator is
-- read from fixed registers and an @n@-bit quotient and @n@-bit
-- remainder are written to those fixed registers. An exception is
-- raised if the denominator is zero or if the quotient does not fit
-- in @n@ bits.
--
-- Also, results should be rounded towards zero. These operations are
-- called @quot@ and @rem@ in Haskell, whereas @div@ and @mod@ in
-- Haskell round towards negative infinity.
--
-- Source: the x86 documentation for @idiv@, Intel x86 manual volume
-- 2A, page 3-393.

-- | Unsigned (@div@ instruction) and signed (@idiv@ instruction) division.
def_div :: InstructionDef
def_div = defUnary "div" $ \_ val -> do
   SomeBV d <- getSomeBVValue val
   case typeWidth d of
    n | Just Refl <- testEquality n n8  -> do
           num <- get ax
           (q,r) <- bvQuotRem ByteRepVal num d
           al .= q
           ah .= r
       | Just Refl <- testEquality n n16 -> do
           num <- bvCat <$> get dx <*> get ax
           (q,r) <- bvQuotRem WordRepVal num d
           ax .= q
           dx .= r
       | Just Refl <- testEquality n n32 -> do
           num <- bvCat <$> get edx <*> get eax
           (q,r) <- bvQuotRem DWordRepVal num d
           eax .= q
           edx .= r
       | Just Refl <- testEquality n n64 -> do
           num <- bvCat <$> get rdx <*> get rax
           (q,r) <- bvQuotRem QWordRepVal num d
           rax .= q
           rdx .= r
       | otherwise -> fail "div: Unknown bit width"

def_idiv :: InstructionDef
def_idiv = defUnary "idiv" $ \_ val -> do
  SomeBV d <- getSomeBVValue val
  set_div_flags
  case typeWidth d of
    n | Just Refl <- testEquality n n8  -> do
           num <- get ax
           (q,r) <- bvSignedQuotRem ByteRepVal num d
           al .= q
           ah .= r
       | Just Refl <- testEquality n n16 -> do
           num <- bvCat <$> get dx <*> get ax
           (q,r) <- bvSignedQuotRem WordRepVal num d
           ax .= q
           dx .= r
       | Just Refl <- testEquality n n32 -> do
           num <- bvCat <$> get edx <*> get eax
           (q,r) <- bvSignedQuotRem DWordRepVal num d
           eax .= q
           edx .= r
       | Just Refl <- testEquality n n64 -> do
           num <- bvCat <$> get rdx <*> get rax
           (q,r) <- bvSignedQuotRem QWordRepVal num d
           rax .= q
           rdx .= r
       | otherwise -> fail "idiv: Unknown bit width"

--  | Execute the halt instruction
--
-- This code assumes that we are not running in kernel mode.
def_hlt :: InstructionDef
def_hlt = defNullary "hlt" $ addArchTermStmt Hlt

def_inc :: InstructionDef
def_inc = defUnary "inc" $ \dstVal -> do
  SomeBV dst <- getSomeBVLocation dstVal
  -- Get current value stored in destination.
  dst_val <- get dst
  let y  = bvLit (typeWidth dst_val) 1
  -- Set overflow and arithmetic flags
  of_loc .= sadd_overflows  dst_val y
  af_loc .= uadd4_overflows dst_val y
  -- no cf_loc
  -- Set result value.
  set_result_value dst (dst_val .+ y)

-- FIXME: is this the right way around?
exec_mul :: forall st ids n
          . (SupportedBVWidth n)
         => Expr ids (BVType n)
         -> X86Generator st ids ()
exec_mul v
  | Just Refl <- testEquality (typeWidth v) n8  = do
    r <- go al
    ax .= r
  | Just Refl <- testEquality (typeWidth v) n16 = do
    (upper, lower) <- bvSplit <$> go ax
    dx .= upper
    ax .= lower
  | Just Refl <- testEquality (typeWidth v) n32 = do
    (upper, lower) <- bvSplit <$> go eax
    edx .= upper
    eax .= lower
  | Just Refl <- testEquality (typeWidth v) n64 = do
    (upper, lower) <- bvSplit <$> go rax
    rdx .= upper
    rax .= lower
  | otherwise =
    fail "mul: Unknown bit width"
  where
    go :: (1 <= n+n, n <= n+n)
       => Location (Addr ids) (BVType n)
       -> X86Generator st ids (BVExpr ids (n+n))
    go l = do
      v' <- get l
      let sz = addNat (typeWidth v) (typeWidth v)
          r  = uext sz v' .* uext sz v -- FIXME: uext here is OK?
          upper_r = fst (bvSplit r) :: Expr ids (BVType n)
      set_undefined sf_loc
      set_undefined af_loc
      set_undefined pf_loc
      set_undefined zf_loc
      let does_overflow = boolNot (is_zero upper_r)
      of_loc .= does_overflow
      cf_loc .= does_overflow
      pure r

really_exec_imul :: forall st ids n
                  . SupportedBVWidth n
                 => BVExpr ids n
                 -> BVExpr ids n
                 -> X86Generator st ids (BVExpr ids (n+n))
really_exec_imul v v' = do
  let w = typeWidth v
  let sz = addNat w w
  let w_is_pos :: LeqProof 1 n
      w_is_pos = LeqProof
  withLeqProof (leqAdd w_is_pos w) $ do
  withLeqProof (addIsLeq w w) $ do
  let r :: BVExpr ids (n+n)
      r  = sext sz v' .* sext sz v
      (_, lower_r :: BVExpr ids n) = bvSplit r
  set_undefined af_loc
  set_undefined pf_loc
  set_undefined zf_loc
  sf_loc .= msb lower_r
  let does_overflow = (r .=/=. sext sz lower_r)
  of_loc .= does_overflow
  cf_loc .= does_overflow
  pure r

exec_imul1 :: forall st ids n . SupportedBVWidth n => BVExpr ids n -> X86Generator st ids ()
exec_imul1 v
  | Just Refl <- testEquality (typeWidth v) n8  = do
      v' <- get al
      r <- really_exec_imul v v'
      ax .= r
  | Just Refl <- testEquality (typeWidth v) n16 = do
      v' <- get ax
      (upper, lower) <- bvSplit <$> really_exec_imul v v'
      dx .= upper
      ax .= lower
  | Just Refl <- testEquality (typeWidth v) n32 = do
      v' <- get eax
      (upper, lower) <- bvSplit <$> really_exec_imul v v'
      edx .= upper
      eax .= lower
  | Just Refl <- testEquality (typeWidth v) n64 = do
      v' <- get rax
      (upper, lower) <- bvSplit <$> really_exec_imul v v'
      rdx .= upper
      rax .= lower
  | otherwise =
      fail "imul: Unknown bit width"

-- FIXME: clag from exec_mul, exec_imul
exec_imul2_3 :: forall st ids n n'
              . (SupportedBVWidth n, 1 <= n', n' <= n)
             => Location (Addr ids) (BVType n)
             -> BVExpr ids n
             -> BVExpr ids n'
             -> X86Generator st ids ()
exec_imul2_3 l v v' = do
  withLeqProof (dblPosIsPos (LeqProof :: LeqProof 1 n)) $ do
  r <- really_exec_imul v (sext (typeWidth v) v')
  l .= snd (bvSplit r)

def_imul :: InstructionDef
def_imul = defVariadic "imul" $ \_ vs ->
  case vs of
    [val] -> do
      SomeBV v <- getSomeBVValue val
      exec_imul1 v
    [loc, val] -> do
      SomeBV l <- getSomeBVLocation loc
      v' <- getSignExtendedValue val (typeWidth l)
      v <- get l
      exec_imul2_3 l v v'
    [loc, val, val'] -> do
      SomeBV l <- getSomeBVLocation loc
      v  <- getBVValue val (typeWidth l)
      SomeBV v' <- getSomeBVValue val'
      Just LeqProof <- return $ testLeq (typeWidth v') (typeWidth v)
      exec_imul2_3 l v v'
    _ ->
      fail "Impossible number of argument in imul"

-- | Should be equiv to 0 - *l
def_neg :: InstructionDef
def_neg = defUnary "neg" $ \_ val -> do
  SomeBV l <- getSomeBVLocation val
  v <- get l
  cf_loc .= boolNot (is_zero v)
  let r = bvNeg v
      zero = bvLit (typeWidth v) 0
  of_loc .= ssub_overflows  zero v
  af_loc .= usub4_overflows zero v
  set_result_value l r

def_sahf :: InstructionDef
def_sahf = defNullary "sahf" $ do
  v <- get ah
  let mk n = bvBit v (bvLit n8 n)
  cf_loc .= mk 0
  pf_loc .= mk 2
  af_loc .= mk 4
  zf_loc .= mk 6
  sf_loc .= mk 7

def_sbb :: InstructionDef
def_sbb = defBinaryLV "sbb" $ \l v -> do
  cf <- get cf_loc
  v0 <- get l
  let w = typeWidth l
  let cbv = mux cf (bvLit w 1) (bvLit w 0)
  let v' = v .+ cbv
  -- Set overflow and arithmetic flags
  of_loc .= ssbb_overflows v0 v cf
  af_loc .= uadd4_overflows v cbv .||. usub4_overflows v0 v'
  cf_loc .= uadd_overflows v cbv .||. (usub_overflows  v0 v')
  -- Set result value.
  let res = v0 .- v'
  set_result_flags res
  l .= res

-- FIXME: duplicates subtraction term by calling exec_cmp
def_sub :: InstructionDef
def_sub = defBinaryLV "sub" $ \l v -> do
  v0 <- get l
  exec_cmp l v -- set flags
  l .= (v0 .- v)

-- ** Decimal Arithmetic Instructions
-- ** Logical Instructions

-- | And two values together.
def_and :: InstructionDef
def_and = defBinaryLV "and" $ \r y -> do
  x <- get r
  let z = x .&. y
  set_bitwise_flags z
  r .= z

exec_or :: Binop
exec_or l v = do
  v' <- get l
  set_undefined af_loc
  of_loc .= false
  cf_loc .= false
  set_result_value l (v' .|. v)

exec_xor :: Binop
exec_xor l v = do
  v0 <- get l
  let r = v0 `bvXor` v
  set_bitwise_flags r
  l .= r

-- ** Shift and Rotate Instructions

exec_sh :: (1 <= n, 8 <= n)
        => RepValSize n -- ^ Number of bits to shift
        -> Location (Addr ids) (BVType n) -- ^ Location to read/write value to shift
        -> F.Value -- ^ 8-bitshift amount
        -> (BVExpr ids n -> BVExpr ids n -> BVExpr ids n)
           -- ^ Function for value
        -> (NatRepr n -> BVExpr ids n -> BVExpr ids 8 -> Expr ids BoolType)
           -- ^ Function to update carry flag
           -- Takes current value of location to shift and number of indices to shift by.
        -> (BVExpr ids n -> BVExpr ids n -> Expr ids BoolType)
           -- ^ Function to update overflow flag
           -- Takes current and new value of location.
        -> X86Generator st ids ()
exec_sh lw l val val_setter cf_setter of_setter = do
  count <-
    case val of
      F.ByteImm i ->
        pure (bvLit n8 (toInteger i))
      F.ByteReg (F.LowReg8 r) -> do
        get $ reg_low8  $ R.X86_GP $ F.Reg64 r
      _ -> fail "Count could not be interpreted."
  v <- get l
  -- The intel manual says that the count is masked to give an upper
  -- bound on the time the shift takes, with a mask of 63 in the case
  -- of a 64 bit operand, and 31 in the other cases.
  let w = typeWidth (repValSizeMemRepr lw)
  let nbits = if intValue w == 64 then 64 else 32
  let low_count = count .&. bvLit n8 (nbits - 1)
  -- Compute result.
  let res = val_setter v (uext (typeWidth v) low_count)
  let zero8 = bvLit n8 0
  -- When the count is zero, nothing happens, in particular, no flags change
  let isNonzero = low_count .=/=. zero8
  -- Set the af flag
  do af_new_val <- make_undefined knownRepr
     modify af_loc $ mux isNonzero af_new_val
  -- Set the overflow flag based on count.
  do of_val   <- get of_loc
     of_undef <- make_undefined knownRepr
     -- If count is zero, then flag is unchanged
     of_loc .= mux (low_count .=. zero8) of_val
                 -- If count is one, then of is xor of initial and final values.
                 (mux (low_count .=. bvLit n8 1) (of_setter v res) of_undef)
  -- Set the carry flag
  modify cf_loc $ mux isNonzero (cf_setter w v low_count)
  -- Set result flags
  modify sf_loc $ mux isNonzero (msb res)
  modify zf_loc $ mux isNonzero (is_zero res)
  p <- even_parity (least_byte res)
  modify pf_loc $ mux isNonzero p
  modify l      $ mux isNonzero res

def_sh :: String
       -> (forall ids n . 1 <= n => BVExpr ids n -> BVExpr ids n -> BVExpr ids n)
          -- ^ Function for value
       -> (forall ids n . (1 <= n, 8 <= n) => NatRepr n -> BVExpr ids n -> BVExpr ids 8 -> Expr ids BoolType)
          -- ^ Function to update carry flag
          -- Takes current value of location to shift and number of indices to shift by.
       -> (forall ids n . (1 <= n) => BVExpr ids n -> BVExpr ids n -> Expr ids BoolType)
          -- ^ Function to update overflow flag
          -- Takes current and new value of location.
       -> InstructionDef
def_sh mnem val_setter cf_setter of_setter = defBinary mnem $ \_ii loc val -> do
  Some (HasRepSize lw l) <- getAddrRegOrSegment loc
  case lw of
    ByteRepVal  -> exec_sh lw l val val_setter cf_setter of_setter
    WordRepVal  -> exec_sh lw l val val_setter cf_setter of_setter
    DWordRepVal -> exec_sh lw l val val_setter cf_setter of_setter
    QWordRepVal -> exec_sh lw l val val_setter cf_setter of_setter

def_shl :: InstructionDef
def_shl = def_sh "shl" bvShl set_cf set_of
  where set_cf w v i =
           (i `bvUle` bvLit n8 (intValue w)) .&&. bvBit v (bvLit w (intValue w) .- uext w i)
        set_of v _ =  msb v

def_shr :: InstructionDef
def_shr = def_sh "shr" bvShr set_cf set_of
  where -- Carry flag should be set to last bit shifted out.
        -- Note that if i exceeds w, bvBit v i returns false, so this does what we want.
        set_cf w v i = bvBit v (uext w i .- bvLit w 1)
        set_of v res = msb res `boolXor` msb v

def_sar :: InstructionDef
def_sar = def_sh "sar" bvSar set_cf set_of
  where -- Set carry flag to last bit shifted out.  This is either the bit at
        -- the index - 1 or the most-significant bit depending on the shift value.
        set_cf w v i = do
          -- Check if w < i
          let notInRange = bvUlt (bvLit n8 (intValue w)) i
          -- Get most-significant bit
          let msb_v = bvBit v (bvLit w (intValue w-1))
          bvBit v (uext w i .- bvLit w 1) .||. (notInRange .&&. msb_v)
        set_of _ _ = false

-- Like def_sh, but for shrd/shxd instructions which have 3 arguments
-- instead of 2.
def_shXd :: String
         -> (forall ids n . 1 <= n => BVExpr ids n -> BVExpr ids n -> BVExpr ids n -> BVExpr ids n)
            -- ^ Function for value.  Takes the source value and the
            -- current value and returns the updated value.
         -> (forall ids n . (1 <= n, 8 <= n) => NatRepr n -> BVExpr ids n -> BVExpr ids 8 -> Expr ids BoolType)
            -- ^ Function to update carry flag. Takes current value of
            -- location to shift and number of indices to shift by.
         -> (forall ids n . (1 <= n) => BVExpr ids n -> BVExpr ids n -> Expr ids BoolType)
            -- ^ Function to update overflow flag.  Takes current and
            -- new value of location.
       -> InstructionDef
def_shXd mnemonic val_setter cf_setter of_setter =
  defTernary mnemonic $ \_ loc srcReg amt -> do
    -- srcVal <- get srcReg
    -- SomeBV srcVal <- getSomeBVValue srcReg
    Some (HasRepSize lw l) <- getAddrRegOrSegment loc
    srcVal <- getBVValue srcReg (typeWidth l)
    case lw of
      ByteRepVal  -> exec_sh lw l amt (val_setter srcVal) cf_setter of_setter
      WordRepVal  -> exec_sh lw l amt (val_setter srcVal) cf_setter of_setter
      DWordRepVal -> exec_sh lw l amt (val_setter srcVal) cf_setter of_setter
      QWordRepVal -> exec_sh lw l amt (val_setter srcVal) cf_setter of_setter

def_shld :: InstructionDef
def_shld = def_shXd "shld" exec_shld set_cf set_of
  where set_cf w v i =
           (i `bvUle` bvLit n8 (intValue w)) .&&. bvBit v (bvLit w (intValue w) .- uext w i)
        set_of v _ =  msb v

exec_shld :: forall n ids . (1 <= n) =>
             BVExpr ids n -> BVExpr ids n -> BVExpr ids n -> BVExpr ids n
exec_shld srcVal v amt = let w = typeWidth v
                         in withLeqProof (dblPosIsPos (LeqProof :: LeqProof 1 n)) $
                            withAddLeq w w $
                            \w2 -> let iv = bvCat v srcVal
                                       amt' = uext w2 amt
                                       fv = bvShl iv amt'
                                   in fst $ bvSplit fv

def_shrd :: InstructionDef
def_shrd = def_shXd "shrd" exec_shrd set_cf set_of
  where -- Carry flag should be set to last bit shifted out.
        -- Note that if i exceeds w, bvBit v i returns false, so this does what we want.
        set_cf w v i = bvBit v (uext w i .- bvLit w 1)
        set_of v res = msb res `boolXor` msb v

exec_shrd :: forall n ids . (1 <= n) =>
             BVExpr ids n -> BVExpr ids n -> BVExpr ids n -> BVExpr ids n
exec_shrd srcVal v amt = let w = typeWidth v
                         in withLeqProof (dblPosIsPos (LeqProof :: LeqProof 1 n)) $
                            withAddLeq w w $
                            \w2 -> let iv = bvCat srcVal v
                                       amt' = uext w2 amt
                                       fv = bvShr iv amt'
                                   in snd $ bvSplit fv

-- FIXME: use really_exec_shift above?
exec_rol :: (1 <= n', n' <= n, SupportedBVWidth n)
         => Location (Addr ids) (BVType n)
         -> BVExpr ids n'
         -> X86Generator st ids ()
exec_rol l count = do
  v    <- get l
  -- The intel manual says that the count is masked to give an upper
  -- bound on the time the shift takes, with a mask of 63 in the case
  -- of a 64 bit operand, and 31 in the other cases.
  let nbits = case testLeq (typeWidth v) n32 of
                Just LeqProof -> 32
                _             -> 64
      countMASK = bvLit (typeWidth v) (nbits - 1)
      low_count = uext (typeWidth v) count .&. countMASK
      -- countMASK is sufficient for 32 and 64 bit operand sizes, but not 16 or
      -- 8, so we need to mask those off again...
      effectiveMASK = bvLit (typeWidth v) (intValue (typeWidth v) - 1)
      effective = uext (typeWidth v) count .&. effectiveMASK
      r = bvRol v effective

  l .= r

  let p = is_zero low_count
  let new_cf = bvBit r (bvLit (typeWidth r) 0)
  -- When the count is zero only the assignment happens (cf and of  is not changed)
  modify cf_loc $ \old_cf -> mux p old_cf new_cf
  u <- make_undefined knownRepr
  modify of_loc $ \old_of ->
      mux p
          old_of
          (mux (low_count .=. bvLit (typeWidth low_count) 1)
               (msb r `boolXor` new_cf)
               u)

-- FIXME: use really_exec_shift above?
exec_ror :: (1 <= n', n' <= n, SupportedBVWidth n)
         => Location (Addr ids) (BVType n)
         -> BVExpr ids n'
         -> X86Generator st ids ()
exec_ror l count = do
  v    <- get l
  -- The intel manual says that the count is masked to give an upper
  -- bound on the time the shift takes, with a mask of 63 in the case
  -- of a 64 bit operand, and 31 in the other cases.
  let nbits = case testLeq (typeWidth v) n32 of
                Just LeqProof -> 32
                Nothing       -> 64
      countMASK = bvLit (typeWidth v) (nbits - 1)
      low_count = uext (typeWidth v) count .&. countMASK
      -- countMASK is sufficient for 32 and 64 bit operand sizes, but not 16 or
      -- 8, so we need to mask those off again...
      effectiveMASK = bvLit (typeWidth v) (intValue (typeWidth v) - 1)
      effective = uext (typeWidth v) count .&. effectiveMASK
      r = bvRor v effective

  l .= r
  let p = is_zero low_count
  let new_cf = bvBit r (bvLit (typeWidth r) (intValue (typeWidth r) - 1))
  modify cf_loc $ \old_cf -> mux p old_cf new_cf
  u <- make_undefined knownRepr
  modify of_loc $ \old_of ->
    mux p old_of $
    mux (low_count .=. bvLit (typeWidth low_count) 1)
        (msb r `boolXor` bvBit r (bvLit (typeWidth r) (intValue (typeWidth v) - 2)))
        u

-- ** Bit and Byte Instructions

getBT16RegOffset :: F.Value -> X86Generator st ids (BVExpr ids 16)
getBT16RegOffset idx =
  case idx of
    F.ByteImm i -> do
      pure $ bvLit n16 $ toInteger $ i Bits..&. 0xF
    F.WordReg ir -> do
      iv <- get $ reg16Loc ir
      pure $ (iv .&. bvLit n16 0xF)
    _ -> error "Unexpected index."

getBT32RegOffset :: F.Value -> X86Generator st ids (BVExpr ids 32)
getBT32RegOffset val =
  case val of
    F.ByteImm i -> do
      pure $ bvLit n32 $ toInteger $ i Bits..&. 0x1F
    F.DWordReg ir -> do
      iv <- get $ reg32Loc ir
      pure $ (iv .&. bvLit n32 0x1F)
    _ -> error "Unexpected index."

getBT64RegOffset :: F.Value -> X86Generator st ids (BVExpr ids 64)
getBT64RegOffset val =
  case val of
    F.ByteImm i -> do
      pure $ bvLit n64 $ toInteger $ i Bits..&. 0x3F
    F.QWordReg ir -> do
      iv <- get $ reg64Loc ir
      pure $ (iv .&. bvLit n64 0x3F)
    _ -> error "Unexpected index."

set_bt_flags :: X86Generator st ids ()
set_bt_flags = do
  set_undefined of_loc
  set_undefined sf_loc
  set_undefined af_loc
  set_undefined pf_loc

-- | Generic function for bt, btc, btr, and bts instructions.
--
-- The first argument is the mnemonic, and action to run.
def_bt :: String
       -> (forall st ids n
           . 1 <= n
           => NatRepr n -- Width of instruction
           -> Location (Addr ids) (BVType n) -- Location to read/write value from
           -> BVExpr ids n -- Index
           -> X86Generator st ids ())
       -> InstructionDef
def_bt mnem act = defBinary mnem $ \_ base_loc idx -> do
  case (base_loc, idx) of
    (F.WordReg r, _) -> do
      iv  <- getBT16RegOffset idx
      act knownNat (reg16Loc r) iv
      set_bt_flags
    (F.DWordReg r, _) -> do
      iv <- getBT32RegOffset idx
      act knownNat (reg32Loc r) iv
      set_bt_flags
    (F.QWordReg r, _) -> do
      iv  <- getBT64RegOffset idx
      act knownNat (reg64Loc r) iv
      set_bt_flags
    (F.Mem16 base, _) -> do
      case idx of
        F.ByteImm i -> do
          when (i >= 16) $ fail $ mnem ++ " given invalid index."
          baseAddr <- getBVAddress base
          let loc = MemoryAddr baseAddr wordMemRepr
          act knownNat loc (bvLit knownNat (toInteger i))
        F.WordReg ir -> do
          off <- get $! reg16Loc ir

          loc <- do
            baseAddr <- getBVAddress base
            let wordOff = sext' n64 $ bvSar off (bvLit knownNat 4)
            pure $! MemoryAddr (baseAddr .+ wordOff) wordMemRepr

          let iv = off .&. bvLit knownNat 15
          act knownNat loc iv
        _ -> error $ "bt given unexpected index."
      set_bt_flags
    (F.Mem32 base, F.ByteImm  i) -> do
      when (i >= 32) $ fail $ mnem ++ " given invalid index."
      loc <- getBV32Addr base
      let iv = bvLit knownNat (toInteger i)
      act knownNat loc iv
      set_bt_flags
    (F.Mem32 base, F.DWordReg  ir) -> do
      off <- get $! reg32Loc ir
      baseAddr <- getBVAddress base
      let dwordOff = sext' n64 $ bvSar off (bvLit knownNat 5)
      let loc = MemoryAddr (baseAddr .+ dwordOff) dwordMemRepr
      let iv  = off .&. bvLit knownNat 31
      act knownNat loc iv
      set_bt_flags
    (F.Mem64 base, F.ByteImm  i) -> do
      when (i >= 64) $ fail $ mnem ++ " given invalid index."
      loc <- getBV64Addr base
      let iv = bvLit knownNat (toInteger i)
      act knownNat loc iv
      set_bt_flags
    (F.Mem64 base, F.QWordReg  ir) -> do
      off <- get $! reg64Loc ir
      let qwordOff = bvSar off (bvLit knownNat 6)
      baseAddr <- getBVAddress base
      let loc = MemoryAddr (baseAddr .+ qwordOff) qwordMemRepr
      let iv = off .&. bvLit knownNat 63
      act knownNat loc iv
      set_bt_flags
    _ -> error $ "bt given unexpected base and index."

def_bsf :: InstructionDef
def_bsf = defBinaryLV "bsf" $ \r y -> do
  zf_loc .= is_zero y
  set_undefined cf_loc
  set_undefined of_loc
  set_undefined sf_loc
  set_undefined af_loc
  set_undefined pf_loc
  r .= bsf y

def_bsr :: InstructionDef
def_bsr = defBinaryLV "bsr" $ \r y -> do
  zf_loc .= is_zero y
  set_undefined cf_loc
  set_undefined of_loc
  set_undefined sf_loc
  set_undefined af_loc
  set_undefined pf_loc
  r .= bsr y

exec_test :: Binop
exec_test l v = do
  v' <- get l
  let r = v' .&. v
  set_bitwise_flags r

def_set_list :: [InstructionDef]
def_set_list =
  defConditionals "set" $ \mnem cc ->
    defUnary mnem $ \_ v -> do
      l <- getBVLocation v n8
      c <- cc
      l .= mux c (bvLit n8 1) (bvLit n8 0)

-- ** Control Transfer Instructions

def_call :: InstructionDef
def_call = defUnary "call" $ \_ v -> do
  -- Push value of next instruction
  old_pc <- getReg R.X86_IP
  push addrRepr old_pc
  -- Set IP
  tgt <- getCallTarget v
  rip .= tgt

-- | Conditional jumps
def_jcc_list :: [InstructionDef]
def_jcc_list =
  defConditionals "j" $ \mnem cc ->
    defUnary mnem $ \_ v -> do
      a <- cc
      doJump a v

def_jmp :: InstructionDef
def_jmp = defUnary "jmp" $ \_ v -> do
  doJump true v

def_ret :: InstructionDef
def_ret = defVariadic "ret"    $ \_ vs ->
  case vs of
    [] -> do
      -- Pop IP and jump to it.
      next_ip <- pop addrRepr
      rip .= next_ip
    [F.WordImm off] -> do
      -- Pop IP and adjust stack pointer.
      next_ip <- pop addrRepr
      modify rsp (bvLit n64 (toInteger off) .+)
      -- Set IP
      rip .= next_ip
    _ ->
      fail "Unexpected number of args to ret"

-- ** String Instructions

-- | MOVS/MOVSB Move string/Move byte string
-- MOVS/MOVSW Move string/Move word string
-- MOVS/MOVSD Move string/Move doubleword string

-- FIXME: probably doesn't work for 32 bit address sizes
-- arguments are only for the size, they are fixed at rsi/rdi

def_movs :: InstructionDef
def_movs = defBinary "movs" $ \ii loc _ -> do
  let pfx = F.iiPrefixes ii
  SomeRepValSize w <- case loc of
    F.Mem8{}  -> pure (SomeRepValSize ByteRepVal)
    F.Mem16{} -> pure (SomeRepValSize WordRepVal)
    F.Mem32{} -> pure (SomeRepValSize DWordRepVal)
    F.Mem64{} -> pure (SomeRepValSize QWordRepVal)
    _ -> error "Bad argument to movs"
  let bytesPerOp = bvLit n64 (repValSizeByteCount w)
  dest <- get rdi
  src  <- get rsi
  df   <- get df_loc
  case pfx^.F.prLockPrefix of
    F.RepPrefix -> do
      when (pfx^.F.prASO) $ do
        fail "Rep prefix semantics not defined when address size override is true."
      -- The direction flag indicates post decrement or post increment.
      count <- get rcx
      addArchStmt =<< traverseF eval (RepMovs w dest src count df)

      -- We adjust rsi and rdi by a negative value if df is true.
      -- The formula is organized so that the bytesPerOp literal is
      -- passed to the multiply and we can avoid non-linear arithmetic.
      let adj = bytesPerOp .* mux df (bvNeg count) count
      rcx .= bvLit n64 (0::Integer)
      rsi .= src  .+ adj
      rdi .= dest .+ adj
    F.NoLockPrefix -> do
      let repr = repValSizeMemRepr w
      -- The direction flag indicates post decrement or post increment.
      v' <- get $ MemoryAddr src repr
      MemoryAddr dest repr .= v'
      -- We adjust rsi and rdi by a negative value if df is true.
      -- The formula is organized so that the bytesPerOp literal is
      -- passed to the multiply and we can avoid non-linear arithmetic.
      let adj = mux df (bvNeg bytesPerOp) bytesPerOp
      rsi .= src  .+ adj
      rdi .= dest .+ adj
    _ -> do
      fail "movs given unsupported lock prefix"


-- | CMPS/CMPSB Compare string/Compare byte string
-- CMPS/CMPSW Compare string/Compare word string
-- CMPS/CMPSD Compare string/Compare doubleword string

exec_cmps :: Bool
          -> RepValSize w
          -> X86Generator st ids ()
exec_cmps repz_pfx rval = repValHasSupportedWidth rval $ do
  let repr = repValSizeMemRepr rval
  -- The direction flag indicates post decrement or post increment.
  df <- get df_loc
  v_rsi <- get rsi
  v_rdi <- get rdi
  let bytesPerOp = memReprBytes repr
  let bytesPerOp' = bvLit n64 bytesPerOp
  if repz_pfx then do
    count <- get rcx
    count_v <- eval count
    src_v   <- eval v_rsi
    dest_v  <- eval v_rdi
    is_reverse_v <- eval df
    nsame <- evalArchFn $ MemCmp bytesPerOp count_v src_v dest_v is_reverse_v
    let equal = (nsame .=. count)
        nwordsSeen = mux equal count (count .- (nsame .+ bvKLit 1))

    -- we need to set the flags as if the last comparison was done, hence this.
    let lastWordBytes = (nwordsSeen .- bvKLit 1) .* bytesPerOp'
    lastSrc1 <- eval $ mux df (v_rsi .- lastWordBytes) (v_rsi .+ lastWordBytes)
    lastSrc2 <- eval $ mux df (v_rdi .- lastWordBytes) (v_rdi .+ lastWordBytes)
    -- we do this to make it obvious so repz cmpsb ; jz ... is clear
    let nbytesSeen = nwordsSeen .* bytesPerOp'

    -- Determine if count ever ran.
    nzCount <- eval $ count .=/=. bvKLit 0

    src1Val <- evalAssignRhs $ CondReadMem repr nzCount lastSrc1 (mkLit knownNat 0)
    src2Val <- evalAssignRhs $ CondReadMem repr nzCount lastSrc2 (mkLit knownNat 0)

    -- Set result value.
    let res = src1Val .- src2Val
    -- Set flags
    pf_val <- even_parity (least_byte res)
    modify of_loc $ mux (ValueExpr nzCount) $ ssub_overflows  src1Val src2Val
    modify af_loc $ mux (ValueExpr nzCount) $ usub4_overflows src1Val src2Val
    modify cf_loc $ mux (ValueExpr nzCount) $ usub_overflows  src1Val src2Val
    modify sf_loc $ mux (ValueExpr nzCount) $ msb res
    modify pf_loc $ mux (ValueExpr nzCount) $ pf_val
    modify rsi    $ mux (ValueExpr nzCount) $ mux df (v_rsi .- nbytesSeen) (v_rsi .+ nbytesSeen)
    modify rdi    $ mux (ValueExpr nzCount) $ mux df (v_rdi .- nbytesSeen) (v_rdi .+ nbytesSeen)
    modify rcx    $ mux (ValueExpr nzCount) $ count .- nwordsSeen
   else do
     v' <- get $ MemoryAddr v_rdi repr
     exec_cmp (MemoryAddr   v_rsi repr) v' -- FIXME: right way around?
     rsi .= mux df (v_rsi  .- bytesPerOp') (v_rsi .+ bytesPerOp')
     rdi .= mux df (v_rdi  .- bytesPerOp') (v_rdi .+ bytesPerOp')


def_cmps :: InstructionDef
def_cmps = defBinary "cmps" $ \ii loc _ -> do
  Some rval <-
    case loc of
      F.Mem8 F.Addr_64{} -> do
        pure $ Some ByteRepVal
      F.Mem16 F.Addr_64{} -> do
        pure $ Some WordRepVal
      F.Mem32 F.Addr_64{} -> do
        pure $ Some DWordRepVal
      F.Mem64 F.Addr_64{} -> do
        pure $ Some QWordRepVal
      _ -> fail "Bad argument to cmps"
  exec_cmps (F.iiLockPrefix ii == F.RepZPrefix) rval

-- SCAS/SCASB Scan string/Scan byte string
-- SCAS/SCASW Scan string/Scan word string
-- SCAS/SCASD Scan string/Scan doubleword string

xaxValLoc :: RepValSize w -> Location a (BVType w)
xaxValLoc ByteRepVal  = al
xaxValLoc WordRepVal  = ax
xaxValLoc DWordRepVal = eax
xaxValLoc QWordRepVal = rax

-- The arguments to this are always rax/QWORD PTR es:[rdi], so we only
-- need the args for the size.
exec_scas :: forall st ids n
          .  Bool -- Flag indicating if RepZPrefix appeared before instruction
          -> Bool -- Flag indicating if RepNZPrefix appeared before instruction
          -> RepValSize n
          -> X86Generator st ids ()
exec_scas True True _val_loc = error "Can't have both Z and NZ prefix"
-- single operation case
exec_scas False False rep = repValHasSupportedWidth rep $ do
  df <- get df_loc
  v_rdi <- get rdi
  v_rax <- get (xaxValLoc rep)
  let memRepr = repValSizeMemRepr rep
  exec_cmp (MemoryAddr v_rdi memRepr) v_rax  -- FIXME: right way around?
  let bytesPerOp = mux df (bvLit n64 (negate (memReprBytes memRepr)))
                          (bvLit n64 (memReprBytes memRepr))
  rdi   .= v_rdi .+ bytesPerOp
-- repz or repnz prefix set
exec_scas _repz_pfx False _rep =
  fail $ "Semantics only currently supports finding elements."
exec_scas _repz_pfx True sz = repValHasSupportedWidth sz $ do
  let val_loc = xaxValLoc sz
  -- Get the direction flag -- it will be used to determine whether to add or subtract at each step.
  -- If the flag is zero, then the register is incremented, otherwise it is incremented.
  df    <- eval =<< get df_loc
  case df of
    BoolValue False ->
      pure ()
    _ ->
      fail $ "Unsupported scas value " ++ show df

  -- Get value that we are using in comparison
  v_rax <- eval =<< get val_loc

  --  Get the starting address for the comparsions
  v_rdi <- eval =<< get rdi
  -- Get maximum number of times to execute instruction
  v_rcx <- eval =<< get rcx
  count' <- evalArchFn (RepnzScas sz v_rax v_rdi v_rcx)
  -- Get number of bytes each comparison will use
  let bytePerOpLit = bvKLit (memReprBytes (repValSizeMemRepr sz))

  -- Count the number of bytes seen.
  let nBytesSeen    = (ValueExpr v_rcx .- count') .* bytePerOpLit

  let lastWordBytes = nBytesSeen .- bytePerOpLit

  let y = ValueExpr v_rax

  dst <- eval (ValueExpr v_rdi .+ lastWordBytes)
  cond <- eval (ValueExpr v_rcx .=/=. bvKLit 0)
  let condExpr = ValueExpr cond
  dst_val <- evalAssignRhs $ CondReadMem (repValSizeMemRepr sz) cond dst (mkLit knownNat 0)

  let condSet :: Location (Addr ids) tp -> Expr ids tp -> X86Generator st ids ()
      condSet l e = modify l (mux condExpr e)

  condSet rcx    count'
  condSet rdi    $ ValueExpr v_rdi .+ nBytesSeen
  condSet of_loc $ ssub_overflows  dst_val y
  -- Set overflow and arithmetic flags
  condSet af_loc $ usub4_overflows dst_val y
  condSet cf_loc $ usub_overflows  dst_val y
  -- Set result value.
  let res = dst_val .- y
  condSet sf_loc $ msb res
  condSet zf_loc $ is_zero res
  byte <- eval (least_byte res)
  condSet pf_loc =<< evalArchFn (EvenParity byte)


def_scas :: InstructionDef
def_scas = defBinary "scas" $ \ii loc loc' -> do
  Some rval <-
    case (loc, loc') of
      (F.ByteReg  F.AL,  F.Mem8  (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement)) -> do
        pure $ Some ByteRepVal
      (F.WordReg  F.AX,  F.Mem16 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement)) -> do
        pure $ Some WordRepVal
      (F.DWordReg F.EAX, F.Mem32 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement)) -> do
        pure $ Some DWordRepVal
      (F.QWordReg F.RAX, F.Mem64 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement)) -> do
        pure $ Some QWordRepVal
      _ -> error $ "scas given bad addrs " ++ show (loc, loc')
  exec_scas (F.iiLockPrefix ii == F.RepZPrefix) (F.iiLockPrefix ii == F.RepNZPrefix) rval

-- LODS/LODSB Load string/Load byte string
-- LODS/LODSW Load string/Load word string
-- LODS/LODSD Load string/Load doubleword string
exec_lods :: 1 <= w
          => Bool -- ^ Flag indicating if RepPrefix appeared before instruction
          -> RepValSize w
          -> X86Generator st ids ()
exec_lods False rep = do
  let mrepr = repValSizeMemRepr rep
  -- The direction flag indicates post decrement or post increment.
  df   <- get df_loc
  src  <- get rsi
  let szv     = bvLit n64 (memReprBytes mrepr)
      neg_szv = bvLit n64 (negate (memReprBytes mrepr))
  v <- get (MemoryAddr src mrepr)
  (xaxValLoc rep) .= v
  rsi .= src .+ mux df neg_szv szv
exec_lods True _rep = error "exec_lods: rep prefix support not implemented"

def_lods :: InstructionDef
def_lods = defBinary "lods" $ \ii loc loc' -> do
  let rep = F.iiLockPrefix ii == F.RepPrefix
  case (loc, loc') of
    (F.Mem8  (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.ByteReg  F.AL) -> do
      exec_lods rep ByteRepVal
    (F.Mem16 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.WordReg  F.AX) -> do
      exec_lods rep WordRepVal
    (F.Mem32 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.DWordReg F.EAX) -> do
      exec_lods rep DWordRepVal
    (F.Mem64 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.QWordReg F.RAX) -> do
      exec_lods rep QWordRepVal
    _ -> error $ "lods given bad arguments " ++ show (loc, loc')

def_lodsx :: (1 <= elsz) => String -> NatRepr elsz -> InstructionDef
def_lodsx suf elsz = defNullaryPrefix ("lods" ++ suf) $ \pfx -> do
  let rep = pfx == F.RepPrefix
  case intValue elsz of
    8  -> exec_lods rep ByteRepVal
    16 -> exec_lods rep WordRepVal
    32 -> exec_lods rep DWordRepVal
    64 -> exec_lods rep QWordRepVal
    _  -> error $ "lodsx given bad size " ++ show (intValue elsz)

-- | STOS/STOSB Store string/Store byte string
-- STOS/STOSW Store string/Store word string
-- STOS/STOSD Store string/Store doubleword string
-- STOS/STOSQ Store string/Store quadword string

def_stos :: InstructionDef
def_stos = defBinary "stos" $ \ii loc loc' -> do
  let pfx = F.iiPrefixes ii
  SomeRepValSize rep <-
    case (loc, loc') of
      (F.Mem8  (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.ByteReg  F.AL) -> do
        pure (SomeRepValSize ByteRepVal)
      (F.Mem16 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.WordReg  F.AX) -> do
        pure (SomeRepValSize WordRepVal)
      (F.Mem32 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.DWordReg F.EAX) -> do
        pure (SomeRepValSize DWordRepVal)
      (F.Mem64 (F.Addr_64 F.ES (Just F.RDI) Nothing F.NoDisplacement), F.QWordReg F.RAX) -> do
        pure (SomeRepValSize QWordRepVal)
      _ -> error $ "stos given bad arguments " ++ show (loc, loc')
  -- The direction flag indicates post decrement or post increment.
  dest <- get rdi
  v    <- get (xaxValLoc rep)
  df   <- get df_loc
  case pfx^.F.prLockPrefix of
    F.RepPrefix -> do
      let mrepr = repValSizeMemRepr rep
      count <- get rcx
      addArchStmt =<< traverseF eval (RepStos rep dest v count df)
      rdi .= dest .+ bvKLit (memReprBytes mrepr) .* mux df (bvNeg count) count
      rcx .= bvKLit 0
    F.NoLockPrefix -> do
        let mrepr = repValSizeMemRepr rep
        let neg_szv = bvLit n64 (negate (memReprBytes mrepr))
        let szv     = bvLit n64 (memReprBytes mrepr)
        MemoryAddr dest mrepr .= v
        rdi .= dest .+ mux df neg_szv szv
    lockPrefix -> fail $ "stos unexpected lock/rep prefix: " ++ show lockPrefix

-- REP        Repeat while ECX not zero
-- REPE/REPZ  Repeat while equal/Repeat while zero
-- REPNE/REPNZ Repeat while not equal/Repeat while not zero

-- ** I/O Instructions
-- ** Enter and Leave Instructions

def_leave :: InstructionDef
def_leave = defNullary  "leave" $ do
  bp_v <- get rbp
  rsp .= bp_v
  bp_v' <- pop addrRepr
  rbp .= bp_v'

-- ** Flag Control (EFLAG) Instructions

-- ** Segment Register Instructions
-- ** Miscellaneous Instructions

def_lea :: InstructionDef
def_lea = defBinary "lea" $ \_ loc (F.VoidMem ar) -> do
  SomeBV l <- getSomeBVLocation loc
  -- ensure that the location is at most 64 bits
  Just LeqProof <- return $ testLeq (typeWidth l) n64
  v <- getBVAddress ar
  l .= bvTrunc (typeWidth l) v

-- ** Random Number Generator Instructions
-- ** BMI1, BMI2

-- * X86 FPU instructions

-- ** Data transfer instructions

-- | FLD Load floating-point value
def_fld :: InstructionDef
def_fld = defUnary "fld" $ \_ val -> do
  case val of
    F.FPMem32 ar -> do
      v <- readMem ar singleMemRepr
      x87Push . bitcast knownRepr =<< evalArchFn (X87_Extend SSE_Single v)
    F.FPMem64 ar -> do
      v <- readMem ar doubleMemRepr
      x87Push . bitcast knownRepr =<< evalArchFn (X87_Extend SSE_Double v)
    F.FPMem80 ar -> do
      l <- getBV80Addr ar
      x87Push =<< get l
    F.X87Register n -> do
      x87Push =<< get (X87StackRegister n)
    _ -> error "fld given unexpected argument"

-- | FST/FSTP Store floating-point value
def_fstX :: String -> Bool -> InstructionDef
def_fstX mnem doPop = defUnary mnem $ \_ val -> do
  v <- get (X87StackRegister 0)
  case val of
    F.FPMem32 ar -> do
      l <- getBVAddress ar
      extv <- evalArchFn . X87_FST SSE_Single =<< eval (bitcast (FloatTypeRepr X86_80FloatRepr) v)
      MemoryAddr l singleMemRepr .= extv
    F.FPMem64 ar -> do
      l <- getBVAddress ar
      extv <- evalArchFn . X87_FST SSE_Double =<< eval (bitcast (FloatTypeRepr X86_80FloatRepr) v)
      MemoryAddr l doubleMemRepr .= extv
    F.FPMem80 ar -> do
      l <- getBVAddress ar
      MemoryAddr l x87MemRepr .= v
    F.X87Register n -> do
      X87StackRegister n .= v
    _ -> fail $ "Bad floating point argument."
  set_undefined c1_loc
  set_undefined c0_loc
  set_undefined c2_loc
  set_undefined c3_loc
  when doPop x87Pop

-- FILD Load integer
-- FIST Store integer
-- FISTP1 Store integer and pop
-- FBLD Load BCD
-- FBSTP Store BCD and pop
-- FXCH Exchange registers
-- FCMOVE Floating-point conditional   move if equal
-- FCMOVNE Floating-point conditional  move if not equal
-- FCMOVB Floating-point conditional   move if below
-- FCMOVBE Floating-point conditional  move if below or equal
-- FCMOVNB Floating-point conditional  move if not below
-- FCMOVNBE Floating-point conditional move if not below or equal
-- FCMOVU Floating-point conditional   move if unordered
-- FCMOVNU Floating-point conditional  move if not unordered

-- ** Basic arithmetic instructions

type X87BinOp
   = forall f
   . f (FloatType X86_80Float)
   -> f (FloatType X86_80Float)
   -> X86PrimFn f (TupleType [FloatType X86_80Float, BoolType])

execX87BinOp :: X87BinOp
             -> Location (Addr ids) (BVType 80)
             -> Expr ids (FloatType X86_80Float)
             -> X86Generator st ids ()
execX87BinOp op loc expr1 = do
  val0 <- eval . bitcast knownRepr =<< get loc
  val1 <- eval expr1
  res <- evalArchFn $ op val0 val1
  loc .= bitcast (BVTypeRepr n80) (app (TupleField knownRepr res P.index0))
  set_undefined c0_loc
  c1_loc .= app (TupleField knownRepr res P.index1)
  set_undefined c2_loc
  set_undefined c3_loc

defX87BinaryInstruction :: String
                        -> X87BinOp
                        -> InstructionDef
defX87BinaryInstruction mnem op =
  defVariadic mnem $ \_ vs -> do
    case vs of
      [F.FPMem32 addr] -> do
        addr' <- getBVAddress addr
        sVal <- eval =<< get (MemoryAddr addr' singleMemRepr)
        val  <- evalArchFn $ X87_Extend SSE_Single sVal
        execX87BinOp op (X87StackRegister 0) val
      [F.FPMem64 addr] -> do
        addr' <- getBVAddress addr
        sVal <- eval =<< get (MemoryAddr addr' doubleMemRepr)
        val  <- evalArchFn $ X87_Extend SSE_Double sVal
        execX87BinOp op (X87StackRegister 0) val
      [F.X87Register x, F.X87Register y] -> do
        val <- get (X87StackRegister y)
        execX87BinOp op (X87StackRegister x) (bitcast knownRepr val)
      _ -> do
        fail $ mnem ++ "had unexpected arguments: " ++ show vs

defX87PopInstruction :: String
                     -> X87BinOp
                     -> InstructionDef
defX87PopInstruction mnem op =
  defVariadic mnem $ \_ vs -> do
    case vs of
      [F.X87Register x, F.X87Register 0] -> do
        val <- get (X87StackRegister 0)
        execX87BinOp op (X87StackRegister x) (bitcast knownRepr val)
        x87Pop
      _ -> do
        fail $ mnem ++ "had unexpected arguments: " ++ show vs

-- | FADD Add floating-point
def_fadd :: InstructionDef
def_fadd = defX87BinaryInstruction "fadd" X87_FAdd

-- FADDP Add floating-point and pop
-- FIADD Add integer

-- | FSUB Subtract floating-point
def_fsub :: InstructionDef
def_fsub = defX87BinaryInstruction "fsub" X87_FSub

-- | FSUBP Subtract floating-point and pop
def_fsubp :: InstructionDef
def_fsubp = defX87PopInstruction "fsubp" X87_FSub

-- FISUB Subtract integer

-- | FSUBR Subtract floating-point reverse
def_fsubr :: InstructionDef
def_fsubr = defX87BinaryInstruction "fsubr" (flip X87_FSub)

-- | FSUBRP Subtract floating-point reverse and pop
def_fsubrp :: InstructionDef
def_fsubrp = defX87PopInstruction "fsubrp" (flip X87_FSub)

-- FISUBR Subtract integer reverse

-- | FMUL Multiply floating-point
def_fmul :: InstructionDef
def_fmul = defX87BinaryInstruction "fmul" X87_FMul

-- FMULP Multiply floating-pAoint and pop
-- FIMUL Multiply integer
-- FDIV Divide floating-point
-- FDIVP Divide floating-point and pop
-- FIDIV Divide integer
-- FDIVR Divide floating-point reverse
-- FDIVRP Divide floating-point reverse and pop
-- FIDIVR Divide integer reverse
-- FPREM Partial remainder
-- FPREM1 IEEE Partial remainder
-- FABS Absolute value
-- FCHS Change sign
-- FRNDINT Round to integer
-- FSCALE Scale by power of two
-- FSQRT Square root
-- FXTRACT Extract exponent and significand

-- ** Comparison instructions

-- FCOM Compare floating-point
-- FCOMP Compare floating-point and pop
-- FCOMPP Compare floating-point and pop twice
-- FUCOM Unordered compare floating-point
-- FUCOMP Unordered compare floating-point and pop
-- FUCOMPP Unordered compare floating-point and pop twice
-- FICOM Compare integer
-- FICOMP Compare integer and pop
-- FCOMI Compare floating-point and set EFLAGS
-- FUCOMI Unordered compare floating-point and set EFLAGS
-- FCOMIP Compare floating-point, set EFLAGS, and pop
-- FUCOMIP Unordered compare floating-point, set EFLAGS, and pop
-- FTST Test floating-point (compare with 0.0)
-- FXAM Examine floating-point

-- ** Transcendental instructions

-- FSIN Sine
-- FCOS Cosine
-- FSINCOS Sine and cosine
-- FPTAN Partial tangent
-- FPATAN Partial arctangent
-- F2XM1 2x − 1
-- FYL2X y∗log2x
-- FYL2XP1 y∗log2(x+1)

-- ** Load constant instructions

-- FLD1 Load +1.0
-- FLDZ Load +0.0
-- FLDPI Load π
-- FLDL2E Load log2e
-- FLDLN2 Load loge2
-- FLDL2T Load log210
-- FLDLG2 Load log102


-- ** x87 FPU control instructions

-- FINCSTP Increment FPU register stack pointer
-- FDECSTP Decrement FPU register stack pointer
-- FFREE Free floating-point register
-- FINIT Initialize FPU after checking error conditions
-- FNINIT Initialize FPU without checking error conditions
-- FCLEX Clear floating-point exception flags after checking for error conditions
-- FNCLEX Clear floating-point exception flags without checking for error conditions
-- FSTCW Store FPU control word after checking error conditions

-- | FNSTCW Store FPU control word without checking error conditions
def_fnstcw :: InstructionDef
def_fnstcw = defUnary "fnstcw" $ \_ loc -> do
  case loc of
    F.Mem16 f_addr -> do
      addr <- getBVAddress f_addr
      set_undefined c0_loc
      set_undefined c1_loc
      set_undefined c2_loc
      set_undefined c3_loc
      fnstcw addr
    _ -> fail $ "fnstcw given bad argument " ++ show loc

-- FLDCW Load FPU control word
-- FSTENV Store FPU environment after checking error conditions
-- FNSTENV Store FPU environment without checking error conditions
-- FLDENV Load FPU environment
-- FSAVE Save FPU state after checking error conditions
-- FNSAVE Save FPU state without checking error conditions
-- FRSTOR Restore FPU state
-- FSTSW Store FPU status word after checking error conditions
-- FNSTSW Store FPU status word without checking error conditions
-- WAIT/FWAIT Wait for FPU
-- FNOP FPU no operation

-- * X87 FPU and SIMD State Management Instructions

-- FXSAVE Save x87 FPU and SIMD state
-- FXRSTOR Restore x87 FPU and SIMD state


-- * MMX Instructions

-- ** MMX Data Transfer Instructions

exec_movd :: (SupportedBVWidth n, 1 <= n')
          => Location (Addr ids) (BVType n)
          -> Expr ids (BVType n')
          -> X86Generator st ids ()
exec_movd l v
  | Just LeqProof <- testLeq  (typeWidth l) (typeWidth v) = l .= bvTrunc (typeWidth l) v
  | Just LeqProof <- testLeq  (typeWidth v) (typeWidth l) = l .=    uext (typeWidth l) v
  | otherwise = fail "movd: Unknown bit width"

-- ** MMX Conversion Instructions

-- PACKSSWB Pack words into bytes with signed saturation
-- PACKSSDW Pack doublewords into words with signed saturation
-- PACKUSWB Pack words into bytes with unsigned saturation

def_punpck :: (1 <= o)
           => String
           -> (forall ids . ([BVExpr ids o], [BVExpr ids o]) -> [BVExpr ids o])
           -> NatRepr o
           -> InstructionDef
def_punpck suf f pieceSize = defBinaryLV ("punpck" ++ suf) $ \l v -> do
  v0 <- get l
  let splitHalf :: [a] -> ([a], [a])
      splitHalf xs = splitAt ((length xs + 1) `div` 2) xs
  let dSplit = f $ splitHalf $ bvVectorize pieceSize v0
      sSplit = f $ splitHalf $ bvVectorize pieceSize v
      r = bvUnvectorize (typeWidth l) $ concat $ zipWith (\a b -> [b, a]) dSplit sSplit
  l .= r

-- ** MMX Packed Arithmetic Instructions

-- | This is used by MMX and SSE instructions
def_packed_binop :: (1 <= w)
                 => String
                 -> NatRepr w
                 -> (Expr ids (BVType w) -> Expr ids (BVType w) -> Expr ids (BVType w))
                 -> InstructionDef
def_packed_binop mnem w f = defBinaryLV mnem $ \l v -> do
  v0 <- get l
  l .= vectorize2 w f v0 v

-- PADDSB Add packed signed byte integers with signed saturation
-- PADDSW Add packed signed word integers with signed saturation
-- PADDUSB Add packed unsigned byte integers with unsigned saturation
-- PADDUSW Add packed unsigned word integers with unsigned saturation

-- PSUBSB Subtract packed signed byte integers with signed saturation
-- PSUBSW Subtract packed signed word integers with signed saturation
-- PSUBUSB Subtract packed unsigned byte integers with unsigned saturation
-- PSUBUSW Subtract packed unsigned word integers with unsigned saturation
-- PMULHW Multiply packed signed word integers and store high result
-- PMULLW Multiply packed signed word integers and store low result
-- PMADDWD Multiply and add packed word integers


-- ** MMX Comparison Instructions

def_pcmp :: 1 <= o
         => String
         -> (forall ids . BVExpr ids o -> BVExpr ids o -> Expr ids BoolType)
         -> NatRepr o
         -> InstructionDef
def_pcmp nm op sz =
  let chkHighLow d s = mux (op d s)  (bvLit sz (negate 1)) (bvLit sz 0)
  def_packed_binop nm sz chkHighLow

-- ** MMX Logical Instructions

exec_pand :: Binop
exec_pand l v = do
  v0 <- get l
  l .= v0 .&. v

exec_pandn :: Binop
exec_pandn l v = do
  v0 <- get l
  l .= bvComplement v0 .&. v

exec_por :: Binop
exec_por l v = do
  v0 <- get l
  l .= v0 .|. v

exec_pxor :: Binop
exec_pxor l v = do
  v0 <- get l
  l .= v0 `bvXor` v


-- ** MMX Shift and Rotate Instructions

-- | PSLLW Shift packed words left logical
-- PSLLD Shift packed doublewords left logical
-- PSLLQ Shift packed quadword left logical

def_psllx :: (1 <= elsz) => String -> NatRepr elsz -> InstructionDef
def_psllx suf elsz = defBinaryLVpoly ("psll" ++ suf) $ \l count -> do
  lv <- get l
  let ls  = bvVectorize elsz lv
      -- This is somewhat tedious: we want to make sure that we don't
      -- truncate e.g. 2^31 to 0, so we saturate if the size is over
      -- the number of bits we want to shift.  We can always fit the
      -- width into count bits (assuming we are passed 16, 32, or 64).
      nbits   = bvLit (typeWidth count) (intValue elsz)
      countsz = case testNatCases (typeWidth count) elsz of
                  NatCaseLT LeqProof -> uext' elsz count
                  NatCaseEQ          -> count
                  NatCaseGT LeqProof -> bvTrunc' elsz count

      ls' = map (\y -> mux (bvUlt count nbits) (bvShl y countsz) (bvLit elsz 0)) ls

  l .= bvUnvectorize (typeWidth l) ls'

-- PSRLW Shift packed words right logical
-- PSRLD Shift packed doublewords right logical
-- PSRLQ Shift packed quadword right logical
-- PSRAW Shift packed words right arithmetic
-- PSRAD Shift packed doublewords right arithmetic


-- ** MMX State Management Instructions

-- EMMS Empty MMX state


-- * SSE Instructions
-- ** SSE SIMD Single-Precision Floating-Point Instructions
-- *** SSE Data Transfer Instructions

def_movsd :: InstructionDef
def_movsd = defBinary "movsd" $ \_ v1 v2 -> do
  case (v1, v2) of
    -- If source is an XMM register then we will leave high order bits alone.
    (F.XMMReg dest, F.XMMReg src) -> do
      vLow <- get (xmm_low64 src)
      xmm_low64 dest .= vLow
    (F.Mem128 src_addr, F.XMMReg src) -> do
      dest <- getBV64Addr src_addr
      vLow <- get (xmm_low64 src)
      dest .= vLow
    -- If destination is an XMM register and source is memory, then zero out
    -- high order bits.
    (F.XMMReg dest, F.Mem128 src_addr) -> do
      v' <- readBV64 =<< getBVAddress src_addr
      xmm_sse dest .= uext n128 v'
    _ ->
      fail $ "Unexpected arguments in FlexdisMatcher.movsd: " ++ show v1 ++ ", " ++ show v2

-- Semantics for SSE movss instruction
def_movss :: InstructionDef
def_movss = defBinary "movss" $ \_ v1 v2 -> do
  case (v1, v2) of
    -- If source is an XMM register then we will leave high order bits alone.
    (F.XMMReg dest, F.XMMReg src) -> do
      vLow <- get (xmm_low32 src)
      xmm_low32 dest .= vLow
    (F.Mem128 f_addr, F.XMMReg src) -> do
      dest <- getBV32Addr f_addr
      vLow <- get (xmm_low32 src)
      dest .= vLow
    -- If destination is an XMM register and source is memory, then zero out
    -- high order bits.
    (F.XMMReg dest, F.Mem128 src_addr) -> do
      vLoc <- readBV32 =<< getBVAddress src_addr
      xmm_sse dest .= uext n128 vLoc
    _ ->
      fail $ "Unexpected arguments in FlexdisMatcher.movss: " ++ show v1 ++ ", " ++ show v2

def_pshufb :: InstructionDef
def_pshufb = defBinary "pshufb" $ \_ f_d f_s -> do
  case (f_d, f_s) of
    (F.XMMReg d, F.XMMReg s) -> do
      dVal <- eval . bitcast knownRepr . bvTrunc' n128 =<< getReg (xmmOwner d)
      sVal <- eval . bitcast knownRepr . bvTrunc' n128 =<< getReg (xmmOwner s)
      r <- evalArchFn $ PShufb SIMDByteCount_XMM dVal sVal
      setLowBits (xmmOwner d) (bitcast (BVTypeRepr n128) r)
    _ -> do
      fail $ "pshufb only supports 2 XMM registers as arguments."

-- MOVAPS Move four aligned packed single-precision floating-point values between XMM registers or between and XMM register and memory
def_movaps :: InstructionDef
def_movaps = defBinaryXMMV "movaps" $ \l v -> l .= v

def_movups :: InstructionDef
def_movups = defBinaryXMMV "movups" $ \l v -> l .= v

-- MOVHPS Move two packed single-precision floating-point values to an from the high quadword of an XMM register and memory
def_movhlps :: InstructionDef
def_movhlps = defBinary "movhlps" $ \_ x y -> do
  case (x, y) of
    (F.XMMReg dst, F.XMMReg src) -> do
      src_val <- get $ xmm_high64 src
      xmm_low64 dst .= src_val
    _ -> fail "Unexpected operands."

def_movhps :: InstructionDef
def_movhps = defBinary "movhps" $ \_ x y -> do
  case (x, y) of
    -- Move high qword of src to dst.
    (F.Mem64 dst_addr, F.XMMReg src) -> do
      src_val <- get $ xmm_high64 src
      dst <- getBV64Addr dst_addr
      dst .= src_val
    -- Move qword at src to high qword of dst.
    (F.XMMReg dst, F.Mem64 src_addr) -> do
      src_val <- readBV64 =<< getBVAddress src_addr
      xmm_high64 dst .= src_val
    _ -> fail "Unexpected operands."

-- MOVLPS Move two packed single-precision floating-point values to an from the low quadword of an XMM register and memory

def_movlhps :: InstructionDef
def_movlhps = defBinary "movlhps" $ \_ x y -> do
  case (x, y) of
    (F.XMMReg dst, F.XMMReg src) -> do
      src_val <- get $ xmm_low64 src
      xmm_high64 dst .= src_val
    _ -> fail "Unexpected operands."

def_movlps :: InstructionDef
def_movlps = defBinary "movlps" $ \_ x y -> do
  case (x, y) of
    -- Move low qword of src to dst.
    (F.Mem64 dst_addr, F.XMMReg src) -> do
      dst <- getBV64Addr dst_addr
      src_val <- get $ xmm_low64 src
      dst .= src_val
    -- Move qword at src to low qword of dst.
    (F.XMMReg dst, F.Mem64 src_addr) -> do
      src_val <- readBV64 =<< getBVAddress src_addr
      xmm_low64 dst .= src_val
    _ -> fail "Unexpected operands."

-- *** SSE Packed Arithmetic Instructions

-- | This evaluates an instruction that takes xmm and xmm/m64 arguments,
-- and applies a function that updates the low 64-bits of the first argument.
def_xmm_ss :: SSE_Op -> InstructionDef
def_xmm_ss f =
  defBinary (sseOpName f ++ "ss") $ \_ (F.XMMReg loc) val -> do
    x <- getXMMreg_float_low loc SSE_Single
    y <- getXMM_float_low    val SSE_Single
    res <- evalArchFn $ SSE_UnaryOp f SSE_Single x y
    setXMMreg_float_low loc SSE_Single res

-- ADDSS Add scalar single-precision floating-point values
def_addss :: InstructionDef
def_addss = def_xmm_ss SSE_Add

-- SUBSS Subtract scalar single-precision floating-point values
def_subss :: InstructionDef
def_subss = def_xmm_ss SSE_Sub

-- MULSS Multiply scalar single-precision floating-point values
def_mulss :: InstructionDef
def_mulss = def_xmm_ss SSE_Mul

-- | DIVSS Divide scalar single-precision floating-point values
def_divss :: InstructionDef
def_divss = def_xmm_ss SSE_Div

-- | This evaluates an instruction that takes xmm and xmm/m128 arguments,
-- and applies a function that updates the register.
def_xmm_packed :: SSE_Op -> InstructionDef
def_xmm_packed f =
  defBinary (sseOpName f ++ "ps") $ \_ (F.XMMReg loc) val -> do
    x <- getXMMreg_sv loc
    y <- getXMM_sv val
    res <- evalArchFn $ SSE_VectorOp f n4 SSE_Single x y
    setXMMreg_sv loc res

-- | ADDPS Add packed single-precision floating-point values
def_addps :: InstructionDef
def_addps = def_xmm_packed SSE_Add

-- SUBPS Subtract packed single-precision floating-point values
def_subps :: InstructionDef
def_subps = def_xmm_packed SSE_Sub

-- | MULPS Multiply packed single-precision floating-point values
def_mulps :: InstructionDef
def_mulps = def_xmm_packed SSE_Mul

-- | DIVPS Divide packed single-precision floating-point values
def_divps :: InstructionDef
def_divps = def_xmm_packed SSE_Div


-- RCPPS Compute reciprocals of packed single-precision floating-point values
-- RCPSS Compute reciprocal of scalar single-precision floating-point values
-- SQRTPS Compute square roots of packed single-precision floating-point values

-- |SQRTSS Compute square root of scalar single-precision floating-point values
def_sqrtss :: InstructionDef
def_sqrtss = def_xmm_ss SSE_Sqrt

-- RSQRTPS Compute reciprocals of square roots of packed single-precision floating-point values
-- RSQRTSS Compute reciprocal of square root of scalar single-precision floating-point values

-- | MINSS Return minimum scalar single-precision floating-point values
def_minss :: InstructionDef
def_minss = def_xmm_ss SSE_Min

-- | MINPS Return minimum packed single-precision floating-point values
def_minps :: InstructionDef
def_minps = def_xmm_packed SSE_Min

-- | MAXSS Return maximum scalar single-precision floating-point values
def_maxss :: InstructionDef
def_maxss = def_xmm_ss SSE_Max

-- | MAXPS Return maximum packed single-precision floating-poi1nt values
def_maxps :: InstructionDef
def_maxps = def_xmm_packed SSE_Max

-- *** SSE Comparison Instructions

-- | UCOMISD Perform unordered comparison of scalar double-precision
-- floating-point values and set flags in EFLAGS register.
def_ucomisd :: InstructionDef
-- Invalid (if SNaN operands), Denormal.
def_ucomisd =
  defBinary "ucomisd" $ \_ xv yv -> do
    x <- getXMM_float_low xv SSE_Double
    y <- getXMM_float_low yv SSE_Double
    res <- evalArchFn (SSE_UCOMIS SSE_Double x y)
    zf_loc .= app (TupleField knownRepr res P.index0)
    pf_loc .= app (TupleField knownRepr res P.index1)
    cf_loc .= app (TupleField knownRepr res P.index2)
    of_loc .= false
    af_loc .= false
    sf_loc .= false

-- CMPPS Compare packed single-precision floating-point values
-- CMPSS Compare scalar single-precision floating-point values
-- COMISS Perform ordered comparison of scalar single-precision floating-point values and set flags in EFLAGS register

-- | UCOMISS Perform unordered comparison of scalar single-precision floating-point values and set flags in EFLAGS register
def_ucomiss :: InstructionDef
-- Invalid (if SNaN operands), Denormal.
def_ucomiss =
  defBinary "ucomiss" $ \_ xv yv -> do
    x <- getXMM_float_low xv SSE_Single
    y <- getXMM_float_low yv SSE_Single
    res <- evalArchFn (SSE_UCOMIS SSE_Single x y)
    zf_loc .= app (TupleField knownRepr res P.index0)
    pf_loc .= app (TupleField knownRepr res P.index1)
    cf_loc .= app (TupleField knownRepr res P.index2)
    of_loc .= false
    af_loc .= false
    sf_loc .= false

-- *** SSE Logical Instructions

def_bifpx :: forall ids elsz
          .  1 <= elsz
           => String
           -> (Expr ids (BVType elsz) -> Expr ids (BVType elsz) -> Expr ids (BVType elsz))
           -> NatRepr elsz
           -> InstructionDef
           -- Location (Addr ids) XMMType
           ---> Expr ids XMMType
           ---> X86Generator st ids ()
def_bifpx mnem f elsz =
  defBinary mnem $ \_ loc val -> do
    l  <- getBVLocation loc n128
    v  <- getBVValue val n128
    fmap_loc (l :: Location (Addr ids) XMMType) $ \lv ->
      vectorize2 elsz f lv (v :: Expr ids XMMType)

-- | ANDPS Perform bitwise logical AND of packed single-precision floating-point values
def_andps :: InstructionDef
def_andps = def_bifpx "andps" (.&.) n32

-- | ANDNPS Perform bitwise logical AND NOT of packed single-precision floating-point values
def_andnps :: InstructionDef
def_andnps = def_bifpx "andnps" (\a b -> bvComplement $ (.&.) a b) n32

-- | ORPS Perform bitwise logical OR of packed single-precision floating-point values
def_orps :: InstructionDef
def_orps = def_bifpx "orps" (.|.) n32

-- | XORPS Perform bitwise logical XOR of packed single-precision floating-point values
def_xorps :: InstructionDef
def_xorps = def_bifpx "xorps" bvXor n32

-- *** SSE Shuffle and Unpack Instructions

-- SHUFPS Shuffles values in packed single-precision floating-point operands
-- UNPCKHPS Unpacks and interleaves the two high-order values from two single-precision floating-point operands

interleave :: [a] -> [a] -> [a]
interleave xs ys = concat (zipWith (\x y -> [x, y]) xs ys)

-- | UNPCKLPS Unpacks and interleaves the two low-order values from two single-precision floating-point operands
def_unpcklps :: InstructionDef
def_unpcklps = defBinaryKnown "unpcklps" exec
  where exec :: Location (Addr ids) XMMType -> Expr ids XMMType -> X86Generator st ids ()
        exec l v = fmap_loc l $ \lv -> do
          let lsd = drop 2 $ bvVectorize n32 lv
              lss = drop 2 $ bvVectorize n32 v
          bvUnvectorize (typeWidth l) (interleave lss lsd)

-- *** SSE Conversion Instructions

-- CVTSI2SS Convert doubleword integer to scalar single-precision floating-point value
def_cvtsi2sX :: String -> SSE_FloatType tp -> InstructionDef
def_cvtsi2sX mnem tp =
  defBinary mnem $ \_ (F.XMMReg loc) val -> do
    -- Loc is RG_XMM_reg
    -- val is "OpType ModRM_rm YSize"
    ev <- getRM32_RM64 val
    -- Read second argument value and coerce to single precision float.
    r <-
      case ev of
        Left  v -> evalArchFn . SSE_CVTSI2SX tp n32 =<< eval =<< get v
        Right v -> evalArchFn . SSE_CVTSI2SX tp n64 =<< eval =<< get v
    setXMMreg_float_low loc tp r

-- CVTPI2PS Convert packed doubleword integers to packed single-precision floating-point values

-- CVTPS2PI Convert packed single-precision floating-point values to packed doubleword integers
-- CVTTPS2PI Convert with truncation packed single-precision floating-point values to packed doubleword integers
-- CVTSS2SI Convert a scalar single-precision floating-point value to a doubleword integer

-- ** SSE MXCSR State Management Instructions

-- LDMXCSR Load MXCSR register
-- STMXCSR Save MXCSR register state

-- ** SSE 64-Bit SIMD Integer Instructions

-- replace pairs with the left operand if `op` is true (e.g., bvUlt for min)
def_pselect :: (1 <= o)
            => String
            -> (forall ids . BVExpr ids o -> BVExpr ids o -> Expr ids BoolType)
            -> NatRepr o
            -> InstructionDef
def_pselect mnem op sz = defBinaryLV mnem $ \l v -> do
  v0 <- get l
  let chkPair d s = mux (d `op` s) d s
  l .= vectorize2 sz chkPair v0 v

-- PAVGB Compute average of packed unsigned byte integers
-- PAVGW Compute average of packed unsigned word integers
-- PEXTRW Extract word

-- | PINSRW Insert word
exec_pinsrw :: Location (Addr ids) XMMType -> BVExpr ids 16 -> Word8 -> X86Generator st ids ()
exec_pinsrw l v off = do
  lv <- get l
  -- FIXME: is this the right way around?
  let ls = bvVectorize n16 lv
      (lower, _ : upper) = splitAt (fromIntegral off - 1) ls
      ls' = lower ++ [v] ++ upper
  l .= bvUnvectorize knownNat ls'

def_pinsrw :: InstructionDef
def_pinsrw = defTernary "pinsrw" $ \_ loc val imm -> do
  l  <- getBVLocation loc knownNat
  v  <- truncateBVValue knownNat =<< getSomeBVValue val
  case imm of
    F.ByteImm off -> exec_pinsrw l v off
    _ -> fail "Bad offset to pinsrw"

-- PMAXUB Maximum of packed unsigned byte integers
-- PMAXSW Maximum of packed signed word integers
-- PMINUB Minimum of packed unsigned byte integers
-- PMINSW Minimum of packed signed word integers
def_pmaxu :: (1 <= w) => String -> NatRepr w -> InstructionDef
def_pmaxu suf w = def_pselect ("pmaxu" ++ suf) (flip bvUlt) w

def_pmaxs :: (1 <= w) => String -> NatRepr w -> InstructionDef
def_pmaxs suf w = def_pselect ("pmaxs" ++ suf) (flip bvSlt) w

def_pminu :: (1 <= w) => String -> NatRepr w -> InstructionDef
def_pminu suf w = def_pselect ("pminu" ++ suf) bvUlt w

def_pmins :: (1 <= w) => String -> NatRepr w -> InstructionDef
def_pmins suf w = def_pselect ("pmins" ++ suf) bvSlt w

exec_pmovmskb :: forall st ids n n'
              .  SupportedBVWidth n
              => Location (Addr ids) (BVType n)
              -> BVExpr ids n'
              -> X86Generator st ids ()
exec_pmovmskb l v
  | Just Refl <- testEquality (typeWidth v) n64 = do
      l .= uext (typeWidth l) (mkMask n8 v)
  | Just LeqProof <- testLeq n32 (typeWidth l)
  , Just Refl <- testEquality (typeWidth v) n128 = do
      let prf = withLeqProof (leqTrans (LeqProof :: LeqProof 16 32)
                                       (LeqProof :: LeqProof 32 n))
      l .= prf (uext (typeWidth l) (mkMask n16 v))
  | otherwise = fail "pmovmskb: Unknown bit width"
  where mkMask sz src = bvUnvectorize sz $ map f $ bvVectorize n8 src
        f b = mux (msb b) (bvLit n1 1) (bvLit n1 0)

-- PMULHUW Multiply packed unsigned integers and store high result
-- PSADBW Compute sum of absolute differences
-- PSHUFW Shuffle packed integer word in MMX register

-- ** SSE Cacheability Control, Prefetch, and Instruction Ordering Instructions

-- MASKMOVQ Non-temporal store of selected bytes from an MMX register into memory
-- MOVNTQ  Non-temporal store of quadword from an MMX register into memory
-- MOVNTPS Non-temporal store of four packed single-precision floating-point
--   values from an XMM register into memory
-- PREFETCHh Load 32 or more of bytes from memory to a selected level of the
--   processor's cache hierarchy
-- SFENCE Serializes store operations

-- * SSE2 Instructions
-- ** SSE2 Packed and Scalar Double-Precision Floating-Point Instructions
-- *** SSE2 Data Movement Instructions

-- | MOVAPD Move two aligned packed double-precision floating-point values
-- between XMM registers or between and XMM register and memory
def_movapd :: InstructionDef
def_movapd = defBinaryXMMV "movapd" $ \l v -> l .= v

-- | MOVUPD Move two unaligned packed double-precision floating-point values
--   between XMM registers or between and XMM register and memory
def_movupd :: InstructionDef
def_movupd = defBinaryXMMV "movupd" $ \l v -> l .= v

def_movhpd :: InstructionDef
def_movhpd = defBinaryLVpoly "movhpd" $ \l v -> do
  v0 <- get l
  let dstPieces = bvVectorize n64 v0
      srcPieces = bvVectorize n64 v
      rPieces = [head srcPieces] ++ (drop 1 dstPieces)
  l .= bvUnvectorize (typeWidth l) rPieces

def_movlpd :: InstructionDef
def_movlpd = defBinaryLVpoly "movlpd" $ \l v -> do
  v0 <- get l
  let dstPieces = bvVectorize n64 v0
      srcPieces = bvVectorize n64 v
      rPieces =  (init dstPieces) ++ [last srcPieces]
  l .= bvUnvectorize (typeWidth l) rPieces

-- MOVMSKPD Extract sign mask from two packed double-precision floating-point values

-- *** SSE2 Packed Arithmetic Instructions

-- | This evaluates an instruction that takes xmm and xmm/m64 arguments,
-- and applies a function that updates the low 64-bits of the first argument.
def_xmm_sd :: SSE_Op
              -- ^ Binary operation
           -> InstructionDef
def_xmm_sd f =
  defBinary (sseOpName f ++ "sd") $ \_ (F.XMMReg loc) val -> do
    x <- getXMMreg_float_low loc SSE_Double
    y <- getXMM_float_low val SSE_Double
    res <- evalArchFn $ SSE_UnaryOp f SSE_Double x y
    setXMMreg_float_low loc SSE_Double res

-- | ADDSD Add scalar double precision floating-point values
def_addsd :: InstructionDef
def_addsd = def_xmm_sd SSE_Add

-- | SUBSD Subtract scalar double-precision floating-point values
def_subsd :: InstructionDef
def_subsd = def_xmm_sd SSE_Sub

-- | MULSD Multiply scalar double-precision floating-point values
def_mulsd :: InstructionDef
def_mulsd = def_xmm_sd SSE_Mul

-- | DIVSD Divide scalar double-precision floating-point values
def_divsd :: InstructionDef
def_divsd = def_xmm_sd SSE_Div

-- ADDPD Add packed double-precision floating-point values
-- SUBPD Subtract scalar double-precision floating-point values
-- MULPD Multiply packed double-precision floating-point values

-- DIVPD Divide packed double-precision floating-point values

-- SQRTPD Compute packed square roots of packed double-precision floating-point values

-- | SQRTSD Compute scalar square root of scalar double-precision floating-point values
def_sqrtsd :: InstructionDef
def_sqrtsd = def_xmm_sd SSE_Sqrt

-- MAXPD Return maximum packed double-precision floating-point values
-- MAXSD Return maximum scalar double-precision floating-point values
-- MINPD Return minimum packed double-precision floating-point values
-- MINSD Return minimum scalar double-precision floating-point values

-- *** SSE2 Logical Instructions

-- | ANDPD  Perform bitwise logical AND of packed double-precision floating-point values
def_andpd :: InstructionDef
def_andpd = def_bifpx "andpd" (.&.) n64

-- ANDNPD Perform bitwise logical AND NOT of packed double-precision floating-point values
-- | ORPD   Perform bitwise logical OR of packed double-precision floating-point values
def_orpd :: InstructionDef
def_orpd = def_bifpx "orpd" (.|.)  n64

-- XORPD  Perform bitwise logical XOR of packed double-precision floating-point values

def_xorpd :: InstructionDef
def_xorpd =
  defBinary "xorpd" $ \_ loc val -> do
    l <- getBVLocation loc n128
    v <- readXMMValue val
    modify l (`bvXor` v)

-- *** SSE2 Compare Instructions

-- CMPPD Compare packed double-precision floating-point values
-- | CMPSD Compare scalar double-precision floating-point values
def_cmpsX :: String -> SSE_FloatType tp -> InstructionDef
def_cmpsX mnem tp =
  defTernary mnem $ \_ (F.XMMReg loc) f_val (F.ByteImm imm) -> do
    f <-
      case lookupSSECmp imm of
        Just f -> pure f
        Nothing -> fail $ mnem ++ " had unsupported operator type " ++ show imm ++ "."
    lv <- getXMMreg_float_low loc tp
    v  <- getXMM_float_low f_val tp
    res <- evalArchFn $ SSE_CMPSX f tp lv v
    let w = floatInfoBits (typeRepr tp)
    case testLeq n1 w of
      Nothing ->
        error "Unexpected width"
      Just LeqProof ->
        xmm_low loc tp .= mux res (bvLit w (-1)) (bvLit w 0)

-- COMISD Perform ordered comparison of scalar double-precision floating-point values and set flags in EFLAGS register


-- *** SSE2 Shuffle and Unpack Instructions

-- CMPPD Compare packed double-precision floating-point values
-- CMPSD Compare scalar double-precision floating-point values
-- COMISD Perform ordered comparison of scalar double-precision floating-point values and set flags in EFLAGS register
-- UCOMISD Perform unordered comparison of scalar double-precision floating-point values and set flags in EFLAGS register.

-- *** SSE2 Conversion Instructions

-- CVTPD2PI  Convert packed double-precision floating-point values to packed doubleword integers.
-- CVTTPD2PI Convert with truncation packed double-precision floating-point values to packed doubleword integers
-- CVTPI2PD  Convert packed doubleword integers to packed double-precision floating-point values
-- CVTPD2DQ  Convert packed double-precision floating-point values to packed doubleword integers
-- CVTTPD2DQ Convert with truncation packed double-precision floating-point values to packed doubleword integers
-- CVTDQ2PD  Convert packed doubleword integers to packed double-precision floating-point values
-- CVTPS2PD  Convert packed single-precision floating-point values to packed double-precision floating- point values
-- CVTPD2PS  Convert packed double-precision floating-point values to packed single-precision floating- point values

-- | CVTSS2SD  Convert scalar single-precision floating-point values to
-- scalar double-precision floating-point values
def_cvtss2sd :: InstructionDef
def_cvtss2sd = defBinary "cvtss2sd" $ \_ (F.XMMReg loc) val -> do
  v <- getXMM_float_low val SSE_Single
  setXMMreg_float_low loc SSE_Double =<< evalArchFn (SSE_CVTSS2SD v)

-- | CVTSD2SS Convert scalar double-precision floating-point values to
-- scalar single-precision floating-point values
def_cvtsd2ss :: InstructionDef
def_cvtsd2ss = defBinary "cvtsd2ss" $ \_ (F.XMMReg loc) val -> do
  v <- getXMM_float_low val SSE_Double
  setXMMreg_float_low loc SSE_Single =<< evalArchFn (SSE_CVTSD2SS v)

-- CVTSD2SI  Convert scalar double-precision floating-point values to a doubleword integer

def_cvttsX2si :: String -> SSE_FloatType tp -> InstructionDef
def_cvttsX2si mnem tp =
  defBinary mnem $ \_ loc val -> do
    v <- getXMM_float_low val tp
    case loc of
      F.DWordReg r ->
        (reg32Loc r .=) =<< evalArchFn (SSE_CVTTSX2SI n32 tp v)
      F.QWordReg r ->
        (reg64Loc r .=) =<< evalArchFn (SSE_CVTTSX2SI n64 tp v)
      _ -> fail "Unexpected operand"

-- ** SSE2 Packed Single-Precision Floating-Point Instructions

-- CVTDQ2PS  Convert packed doubleword integers to packed single-precision floating-point values
-- CVTPS2DQ  Convert packed single-precision floating-point values to packed doubleword integers
-- CVTTPS2DQ Convert with truncation packed single-precision floating-point values to packed doubleword integers

-- ** SSE2 128-Bit SIMD Integer Instructions

-- | MOVDQA Move aligned double quadword.

-- FIXME: exception on unaligned loads
def_movdqa :: InstructionDef
def_movdqa = defBinaryXMMV "movdqa" $ \l v -> l .= v

-- | MOVDQU Move unaligned double quadword

-- FIXME: no exception on unaligned loads
def_movdqu :: InstructionDef
def_movdqu = defBinaryXMMV "movdqu" $ \l v -> l .= v

-- MOVQ2DQ Move quadword integer from MMX to XMM registers
-- MOVDQ2Q Move quadword integer from XMM to MMX registers
-- PMULUDQ Multiply packed unsigned doubleword integers

-- PSUBQ Subtract packed quadword integers
-- PSHUFLW Shuffle packed low words
-- PSHUFHW Shuffle packed high words

exec_pshufd :: forall st ids n k
            .  (SupportedBVWidth n, 1 <= k)
            => Location (Addr ids) (BVType n)
            -> BVExpr ids n
            -> BVExpr ids k
            -> X86Generator st ids ()
exec_pshufd l v imm
  | Just Refl <- testEquality (typeWidth imm) n8 = do
      let shiftAmt :: BVExpr ids 2 -> BVExpr ids 128
          shiftAmt pieceID = (uext n128 pieceID .*) $ bvLit n128 32

          getPiece :: BVExpr ids 128 -> BVExpr ids 2 -> BVExpr ids 32
          getPiece src pieceID = bvTrunc n32 $ src `bvShr` (shiftAmt pieceID)

      let order = bvVectorize (addNat n1 n1) imm
          dstPieces = concatMap (\src128 -> map (getPiece src128) order) $ bvVectorize n128 v
      l .= bvUnvectorize (typeWidth l) dstPieces
  | otherwise = fail "pshufd: Unknown bit width"

def_pslldq :: InstructionDef
def_pslldq = defBinaryLVge "pslldq" $ \l v -> do
  v0 <- get l
  -- temp is 16 if v is greater than 15, otherwise v
  let not15 = bvComplement $ bvLit (typeWidth v) 15
      temp = mux (is_zero $ not15 .&. v)
                 (uext (typeWidth v0) v)
                 (bvLit (typeWidth v0) 16)
  l .= v0 `bvShl` (temp .* bvLit (typeWidth v0) 8)

-- PSRLDQ Shift double quadword right logical
-- PUNPCKHQDQ Unpack high quadwords
-- PUNPCKLQDQ Unpack low quadwords

-- ** SSE2 Cacheability Control and Ordering Instructions


-- CLFLUSH Flushes and invalidates a memory operand and its associated cache line from all levels of the processor’s cache hierarchy
-- LFENCE Serializes load operations
-- MFENCE Serializes load and store operations
-- PAUSE      Improves the performance of “spin-wait loops”
-- MASKMOVDQU Non-temporal store of selected bytes from an XMM register into memory
-- MOVNTPD    Non-temporal store of two packed double-precision floating-point values from an XMM register into memory
-- MOVNTDQ    Non-temporal store of double quadword from an XMM register into memory
-- MOVNTI     Non-temporal store of a doubleword from a general-purpose register into memory

-- * SSE3 Instructions
-- ** SSE3 x87-FP Integer Conversion Instruction

-- FISTTP Behaves like the FISTP instruction but uses truncation, irrespective of the rounding mode specified in the floating-point control word (FCW)

-- ** SSE3 Specialized 128-bit Unaligned Data Load Instruction

def_lddqu :: InstructionDef
def_lddqu = defBinary "lddqu"  $ \_ loc val -> do
  l <- getBVLocation loc n128
  v <- case val of
    F.VoidMem a -> readBVAddress a xmmMemRepr
    _ -> fail "readVoidMem given bad address."
  l .= v

-- ** SSE3 SIMD Floating-Point Packed ADD/SUB Instructions

-- ADDSUBPS Performs single-precision addition on the second and fourth pairs of 32-bit data elements within the operands; single-precision subtraction on the first and third pairs
-- ADDSUBPD Performs double-precision addition on the second pair of quadwords, and double-precision subtraction on the first pair

-- ** SSE3 SIMD Floating-Point Horizontal ADD/SUB Instructions

-- HADDPS Performs a single-precision addition on contiguous data elements. The first data element of the result is obtained by adding the first and second elements of the first operand; the second element by adding the third and fourth elements of the first operand; the third by adding the first and second elements of the second operand; and the fourth by adding the third and fourth elements of the second operand.
-- HSUBPS Performs a single-precision subtraction on contiguous data elements. The first data element of the result is obtained by subtracting the second element of the first operand from the first element of the first operand; the second element by subtracting the fourth element of the first operand from the third element of the first operand; the third by subtracting the second element of the second operand from the first element of the second operand; and the fourth by subtracting the fourth element of the second operand from the third element of the second operand.
-- HADDPD Performs a double-precision addition on contiguous data elements. The first data element of the result is obtained by adding the first and second elements of the first operand; the second element by adding the first and second elements of the second operand.
-- HSUBPD Performs a double-precision subtraction on contiguous data elements. The first data element of the result is obtained by subtracting the second element of the first operand from the first element of the first operand; the second element by subtracting the second element of the second operand from the first element of the second operand.


-- ** SSE3 SIMD Floating-Point LOAD/MOVE/DUPLICATE Instructions

-- MOVSHDUP Loads/moves 128 bits; duplicating the second and fourth 32-bit data elements
-- MOVSLDUP Loads/moves 128 bits; duplicating the first and third 32-bit data elements
-- MOVDDUP Loads/moves 64 bits (bits[63:0] if the source is a register) and returns the same 64 bits in both the lower and upper halves of the 128-bit result register; duplicates the 64 bits from the source

-- ** SSE3 Agent Synchronization Instructions

-- MONITOR Sets up an address range used to monitor write-back stores
-- MWAIT Enables a logical processor to enter into an optimized state while waiting for a write-back store to the address range set up by the MONITOR instruction


-- * Supplemental Streaming SIMD Extensions 3 (SSSE3) Instructions
-- ** Horizontal Addition/Subtraction

-- PHADDW Adds two adjacent, signed 16-bit integers horizontally from the source and destination operands and packs the signed 16-bit results to the destination operand.
-- PHADDSW Adds two adjacent, signed 16-bit integers horizontally from the source and destination operands and packs the signed, saturated 16-bit results to the destination operand.
-- PHADDD Adds two adjacent, signed 32-bit integers horizontally from the source and destination operands and packs the signed 32-bit results to the destination operand.
-- PHSUBW Performs horizontal subtraction on each adjacent pair of 16-bit signed integers by subtracting the most significant word from the least significant word of each pair in the source and destination operands. The signed 16-bit results are packed and written to the destination operand.
-- PHSUBSW Performs horizontal subtraction on each adjacent pair of 16-bit signed integers by subtracting the most significant word from the least significant word of each pair in the source and destination operands. The signed, saturated 16-bit results are packed and written to the destination operand.
-- PHSUBD Performs horizontal subtraction on each adjacent pair of 32-bit signed integers by subtracting the most significant doubleword from the least significant double word of each pair in the source and destination operands. The signed 32-bit results are packed and written to the destination operand.

-- ** Packed Absolute Values

-- PABSB Computes the absolute value of each signed byte data element.
-- PABSW Computes the absolute value of each signed 16-bit data element.
-- PABSD Computes the absolute value of each signed 32-bit data element.

-- ** Multiply and Add Packed Signed and Unsigned Bytes

-- PMADDUBSW Multiplies each unsigned byte value with the corresponding signed byte value to produce an intermediate, 16-bit signed integer. Each adjacent pair of 16-bit signed values are added horizontally. The signed, saturated 16-bit results are packed to the destination operand.

-- ** Packed Multiply High with Round and Scale

-- PMULHRSW Multiplies vertically each signed 16-bit integer from the destination operand with the corresponding signed 16-bit integer of the source operand, producing intermediate, signed 32-bit integers. Each intermediate 32-bit integer is truncated to the 18 most significant bits. Rounding is always performed by adding 1 to the least significant bit of the 18-bit intermediate result. The final result is obtained by selecting the 16 bits immediately to the right of the most significant bit of each 18-bit intermediate result and packed to the destination operand.

-- ** Packed Shuffle Bytes

-- PSHUFB Permutes each byte in place, according to a shuffle control mask. The least significant three or four bits of each shuffle control byte of the control mask form the shuffle index. The shuffle mask is unaffected. If the most significant bit (bit 7) of a shuffle control byte is set, the constant zero is written in the result byte.


-- ** Packed Sign

-- PSIGNB/W/D Negates each signed integer element of the destination operand if the sign of the corresponding data element in the source operand is less than zero.

-- ** Packed Align Right

exec_palignr :: forall st ids n k
             . (SupportedBVWidth n, 1 <= k, k <= n)
             => Location (Addr ids) (BVType n)
             -> BVExpr ids n
             -> BVExpr ids k
             -> X86Generator st ids ()
exec_palignr l v imm = do
  v0 <- get l

  -- 1 <= n+n, given 1 <= n
  withLeqProof (dblPosIsPos (LeqProof :: LeqProof 1 n)) $ do
  -- k <= (n+n), given k <= n and n <= n+n
  withLeqProof (leqTrans k_leq_n (leqAdd (leqRefl n) n)) $ do

  -- imm is # of bytes to shift, so multiply by 8 for bits to shift
  let n_plus_n = addNat (typeWidth v) (typeWidth v)
      shiftAmt = uext n_plus_n imm .* bvLit n_plus_n 8

  let (_, lower) = bvSplit $ (v0 `bvCat` v) `bvShr` shiftAmt
  l .= lower

  where n :: Proxy n
        n = Proxy
        k_leq_n :: LeqProof k n
        k_leq_n = LeqProof

def_syscall :: InstructionDef
def_syscall =
  defNullary "syscall" $
    addArchTermStmt X86Syscall

def_cpuid :: InstructionDef
def_cpuid =
  defNullary "cpuid"   $ do
    eax_val <- eval =<< get eax
    -- Call CPUID and get a 128-bit value back.
    res <- evalArchFn (CPUID eax_val)
    eax .= bvTrunc n32 res
    ebx .= bvTrunc n32 (res `bvShr` bvLit n128 32)
    ecx .= bvTrunc n32 (res `bvShr` bvLit n128 64)
    edx .= bvTrunc n32 (res `bvShr` bvLit n128 96)

def_rdtsc :: InstructionDef
def_rdtsc =
  defNullary "rdtsc" $ do
    res <- evalArchFn RDTSC
    edx .= bvTrunc n32 (res `bvShr` bvLit n64 32)
    eax .= bvTrunc n32 res

def_xgetbv :: InstructionDef
def_xgetbv =
  defNullary "xgetbv" $ do
    ecx_val <- eval =<< get ecx
    res <- evalArchFn (XGetBV ecx_val)
    edx .= bvTrunc n32 (res `bvShr` bvLit n64 32)
    eax .= bvTrunc n32 res

------------------------------------------------------------------------
-- AVX instructions










------------------------------------------------------------------------
-- Instruction list


all_instructions :: [InstructionDef]
all_instructions =
  [ def_lea
  , def_call
  , def_jmp
  , def_ret
  , def_cwd
  , def_cdq
  , def_cqo
  , def_movsx
  , def_movsxd
  , def_movzx
  , def_xchg
  , def_cmps
  , def_movs
  , def_lods
  , def_lodsx "b" n8
  , def_lodsx "w" n16
  , def_lodsx "d" n32
  , def_lodsx "q" n64
  , def_stos
  , def_scas

    -- fixed size instructions.  We truncate in the case of
    -- an xmm register, for example
  , def_addsd
  , def_subsd
  , def_movsd
  , def_movapd
  , def_movaps
  , def_movups
  , def_movupd
  , def_movdqa
  , def_movdqu
  , def_movss
  , def_mulsd
  , def_divsd
  , def_psllx "w" n16
  , def_psllx "d" n32
  , def_psllx "q" n64
  , def_ucomisd
  , def_xorpd
  , def_xorps

  , def_cvtss2sd
  , def_cvtsd2ss
  , def_cvtsi2sX "cvtsi2sd" SSE_Double
  , def_cvtsi2sX "cvtsi2ss" SSE_Single
  , def_cvttsX2si "cvttsd2si" SSE_Double
  , def_cvttsX2si "cvttss2si" SSE_Single
  , def_pinsrw
  , def_cmpsX "cmpsd" SSE_Double
  , def_cmpsX "cmpss" SSE_Single
  , def_andpd
  , def_orpd
  , def_unpcklps

    -- regular instructions
  , def_adc
  , defBinaryLV "add" exec_add
  , def_and
  , def_bt "bt" $ \_ loc idx -> do
      val <- get loc
      cf_loc .= bvBit val idx
  , def_bt "btc" $ \w loc idx -> do
      val <- get loc
      loc .= bvXor val ((bvLit w 1) `bvShl` idx)
      cf_loc .= bvBit val idx
  , def_bt "btr" $ \w loc idx -> do
      val <- get loc
      loc .= val .&. bvComplement ((bvLit w 1) `bvShl` idx)
      cf_loc .= bvBit val idx
  , def_bt "bts" $ \w loc idx -> do
      val <- get loc
      loc .= val .|. ((bvLit w 1) `bvShl` idx)
      cf_loc .= bvBit val idx
  , def_bsf
  , def_bsr
  , def_bswap
  , def_cbw
  , def_cwde
  , def_cdqe
  , defNullary  "clc"  $ cf_loc .= false
  , defNullary  "cld"  $ df_loc .= false
  , defBinaryLV "cmp"   exec_cmp
  , def_dec
  , def_div
  , def_hlt
  , def_idiv
  , def_imul
  , def_inc
  , def_leave
  , def_mov
  , defUnary   "mul"   $ \_ val -> do
      SomeBV v <- getSomeBVValue val
      exec_mul v
  , def_neg
  , defNullary  "nop"   $ return ()
  , defUnary "not"   $ \_ val -> do
      SomeBV l <- getSomeBVLocation val
      modify l bvComplement
  , defBinaryLV "or"    $ exec_or
  , defNullary "pause"  $ return ()
  , def_pop

  , def_cmpxchg
  , def_cmpxchg8b
  , def_push
  , defBinaryLVge "rol"  exec_rol
  , defBinaryLVge "ror"  exec_ror
  , def_sahf
  , def_sbb
  , def_shl
  , def_shr
  , def_shld
  , def_shrd
  , def_sar
  , defNullary  "std" $ df_loc .= true
  , def_sub
  , defBinaryLV "test" exec_test
  , def_xadd
  , defBinaryLV "xor" exec_xor

  , defNullary "ud2" $ addArchTermStmt UD2

    -- Primitive instructions
  , def_syscall
  , def_cpuid
  , def_rdtsc
  , def_xgetbv

    -- MMX instructions
  , defBinaryLVpoly "movd" exec_movd
  , defBinaryLVpoly "movq" exec_movd

  , def_punpck "hbw"  fst  n8
  , def_punpck "hwd"  fst n16
  , def_punpck "hdq"  fst n32
  , def_punpck "hqdq" fst n64

  , def_punpck "lbw"  snd  n8
  , def_punpck "lwd"  snd n16
  , def_punpck "ldq"  snd n32
  , def_punpck "lqdq" snd n64

  , def_packed_binop "paddb" n8  (.+)
  , def_packed_binop "paddw" n16 (.+)
  , def_packed_binop "paddd" n32 (.+)
  , def_packed_binop "paddq" n64 (.+)

  , def_packed_binop "psubb" n8  (.-)
  , def_packed_binop "psubw" n16 (.-)
  , def_packed_binop "psubd" n32 (.-)

  , def_pcmp "pcmpeqb" (.=.) n8
  , def_pcmp "pcmpeqw" (.=.) n16
  , def_pcmp "pcmpeqd" (.=.) n32

  , def_pcmp "pcmpgtb" (flip bvSlt) n8
  , def_pcmp "pcmpgtw" (flip bvSlt) n16
  , def_pcmp "pcmpgtd" (flip bvSlt) n32

  , defBinaryLV "pand"       $ exec_pand
  , defBinaryLV "pandn"      $ exec_pandn
  , defBinaryLV "por"        $ exec_por
  , defBinaryLV "pxor"       $ exec_pxor

    -- SSE instructions
  , def_movhlps
  , def_movhps
  , def_movlhps
  , def_movlps
    -- SSE Packed
  , def_addps
  , def_subps
  , def_mulps
  , def_divps
  , def_addss
  , def_subss
  , def_mulss
  , def_divss
  , def_minss
  , def_sqrtss
  , def_sqrtsd
  , def_minps
  , def_maxss
  , def_maxps
    -- SSE Comparison
  , def_ucomiss
    -- SSE Logical
  , def_andps
  , def_andnps
  , def_orps

  , def_pmaxu "b"  n8
  , def_pmaxu "w" n16
  , def_pmaxu "d" n32

  , def_pmaxs "b"  n8
  , def_pmaxs "w" n16
  , def_pmaxs "d" n32

  , def_pminu "b"  n8
  , def_pminu "w" n16
  , def_pminu "d" n32

  , def_pmins "b"  n8
  , def_pmins "w" n16
  , def_pmins "d" n32

  , defBinaryLVpoly "pmovmskb" exec_pmovmskb
  , def_movhpd
  , def_movlpd
  , def_pshufb

  , defTernaryLVV  "pshufd" exec_pshufd
  , def_pslldq
  , def_lddqu
  , defTernaryLVV "palignr" exec_palignr
    -- X87 FP instructions
  , def_fadd
  , def_fld
  , def_fmul
  , def_fnstcw -- stores to bv memory (i.e., not FP)
  , def_fstX "fst"  False
  , def_fstX "fstp" True
  , def_fsub
  , def_fsubp
  , def_fsubr
  , def_fsubrp
  , defNullary "emms" $ addArchStmt EMMS
  , defNullary "femms" $ addArchStmt EMMS
  ]
  ++ def_cmov_list
  ++ def_jcc_list
  ++ def_set_list
  ++ AVX.all_instructions

------------------------------------------------------------------------
-- execInstruction

mapNoDupFromList :: (Ord k, Show k) => [(k,v)] -> Either k (Map k v)
mapNoDupFromList = foldlM ins M.empty
  where ins m (k,v) =
          case M.lookup k m of
            Just _ -> Left k
            Nothing -> Right (M.insert k v m)

-- | A map from instruction mnemonics to their semantic definitions
semanticsMap :: Map String InstructionSemantics
semanticsMap =
  case mapNoDupFromList all_instructions of
    Right m -> m
    Left k -> error $ "semanticsMap contains duplicate entries for " ++ show k ++ "."

-- | Execute an instruction if definined in the map or return nothing.
execInstruction :: Expr ids (BVType 64)
                   -- ^ Next ip address
                -> F.InstructionInstance
                -> Maybe (X86Generator st ids ())
execInstruction next ii =
  case M.lookup (F.iiOp ii) semanticsMap of
    Just (InstructionSemantics f) -> Just $ do
      rip .= next
      f ii
    Nothing -> Nothing
