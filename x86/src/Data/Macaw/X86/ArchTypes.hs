{-
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This defines the X86_64 architecture type and the supporting definitions.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.X86.ArchTypes
  ( -- * Architecture
    X86_64
  , UCOMType(..)
  , X86PrimFn(..)
  , rewriteX86PrimFn
  , x86PrimFnHasSideEffects
  , X86Stmt(..)
  , rewriteX86Stmt
  , X86TermStmt(..)
  , rewriteX86TermStmt
  , X86PrimLoc(..)
  , SIMDWidth(..)
  , RepValSize(..)
  , repValSizeByteCount
  , repValSizeMemRepr
  ) where

import           Data.Bits
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Rewriter
import           Data.Macaw.Memory (Endianness(..))
import           Data.Macaw.Types
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import qualified Flexdis86 as F
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.X86.X86Reg
import           Data.Macaw.X86.X87ControlReg

------------------------------------------------------------------------
-- SIMDWidth

-- | Defines a width of a register associated with SIMD operations
-- (e.g., MMX, XMM, AVX)
data SIMDWidth w
   = (w ~  64) => SIMD_64
   | (w ~ 128) => SIMD_128
   | (w ~ 256) => SIMD_256

-- | Return the 'NatRepr' associated with the given width.
instance HasRepr SIMDWidth NatRepr where
  typeRepr SIMD_64  = knownNat
  typeRepr SIMD_128 = knownNat
  typeRepr SIMD_256 = knownNat

------------------------------------------------------------------------
-- RepValSize

-- | Rep value
data RepValSize w
   = (w ~  8) => ByteRepVal
   | (w ~ 16) => WordRepVal
   | (w ~ 32) => DWordRepVal
   | (w ~ 64) => QWordRepVal

repValSizeMemRepr :: RepValSize w -> MemRepr (BVType w)
repValSizeMemRepr v =
  case v of
    ByteRepVal  -> BVMemRepr (knownNat :: NatRepr 1) LittleEndian
    WordRepVal  -> BVMemRepr (knownNat :: NatRepr 2) LittleEndian
    DWordRepVal -> BVMemRepr (knownNat :: NatRepr 4) LittleEndian
    QWordRepVal -> BVMemRepr (knownNat :: NatRepr 8) LittleEndian

repValSizeByteCount :: RepValSize w -> Integer
repValSizeByteCount = memReprBytes . repValSizeMemRepr

------------------------------------------------------------------------
-- X86TermStmt

data X86TermStmt ids = X86Syscall

instance PrettyF X86TermStmt where
  prettyF X86Syscall = text "x86_syscall"

------------------------------------------------------------------------
-- X86PrimLoc

-- | This describes a primitive location that can be read or written to in the
--  X86 architecture model.
-- Primitive locations are not modeled as registers, but rather as implicit state.
data X86PrimLoc tp
   = (tp ~ BVType 64) => ControlLoc !F.ControlReg
   | (tp ~ BVType 64) => DebugLoc   !F.DebugReg
   | (tp ~ BVType 16) => FS
     -- ^ This refers to the selector of the 'FS' register.
   | (tp ~ BVType 16) => GS
     -- ^ This refers to the se lector of the 'GS' register.
   | forall w . (tp ~ BVType   w) => X87_ControlLoc !(X87_ControlReg w)
     -- ^ One of the x87 control registers

instance HasRepr X86PrimLoc TypeRepr where
  typeRepr ControlLoc{} = knownType
  typeRepr DebugLoc{}   = knownType
  typeRepr FS = knownType
  typeRepr GS = knownType
  typeRepr (X87_ControlLoc r) =
    case x87ControlRegWidthIsPos r of
      LeqProof -> BVTypeRepr (typeRepr r)

instance Pretty (X86PrimLoc tp) where
  pretty (ControlLoc r) = text (show r)
  pretty (DebugLoc r) = text (show r)
  pretty FS = text "fs"
  pretty GS = text "gs"
  pretty (X87_ControlLoc r) = text (show r)

------------------------------------------------------------------------
-- X86PrimFn

-- | Defines primitive functions in the X86 format.
data X86PrimFn f tp where
  EvenParity :: !(f (BVType 8)) -> X86PrimFn f BoolType
  -- ^ Return true if least-significant bit has even number of bits set.
  ReadLoc :: !(X86PrimLoc tp) -> X86PrimFn f tp
  -- ^ Read from a primitive X86 location
  ReadFSBase :: X86PrimFn f (BVType 64)
  -- ^ Read the 'FS' base address
  ReadGSBase :: X86PrimFn f (BVType 64)
  -- ^ Read the 'GS' base address
  CPUID :: !(f (BVType 32)) -> X86PrimFn f (BVType 128)
  -- ^ The CPUID instruction
  --
  -- Given value in eax register, this returns the concatenation of eax:ebx:ecx:edx.
  RDTSC :: X86PrimFn f (BVType 64)
  -- ^ The RDTSC instruction
  --
  -- This returns the current time stamp counter a 64-bit value that will
  -- be stored in edx:eax
  XGetBV :: !(f (BVType 32)) -> X86PrimFn f (BVType 64)
  -- ^ The XGetBV instruction primitive
  --
  -- This returns the extended control register defined in the given value
  -- as a 64-bit value that will be stored in edx:eax
  PShufb :: (1 <= w) => !(SIMDWidth w) -> !(f (BVType w)) -> !(f (BVType w)) -> X86PrimFn f (BVType w)
  -- ^ @PShufb w x s@ returns a value @res@ generated from the bytes of @x@
  -- based on indices defined in the corresponding bytes of @s@.
  --
  -- Let @n@ be the number of bytes in the width @w@, and let @l = log2(n)@.
  -- Given a byte index @i@, the value of byte @res[i]@, is defined by
  --   @res[i] = 0 if msb(s[i]) == 1@
  --   @res[i] = x[j] where j = s[i](0..l)
  -- where @msb(y)@ returns the most-significant bit in byte @y@.
  MemCmp :: !Integer
           -- /\ Number of bytes per value.
         -> !(f (BVType 64))
           -- /\ Number of values to compare
         -> !(f (BVType 64))
           -- /\ Pointer to first buffer.
         -> !(f (BVType 64))
           -- /\ Pointer to second buffer.
         -> !(f BoolType)
           -- /\ Direction flag, False means increasing
         -> X86PrimFn f (BVType 64)

  -- ^ Compares to memory regions
  RepnzScas :: !(RepValSize n)
            -> !(f (BVType n))
            -> !(f (BVType 64))
            -> !(f (BVType 64))
            -> X86PrimFn f (BVType 64)
  -- ^ `RepnzScas sz val base cnt` searchs through a buffer starting at
  -- `base` to find  an element `i` such that base[i] = val.
  -- Each step it increments `i` by 1 and decrements `cnt` by `1`.
  -- It returns the final value of `cnt`, the
  MMXExtend :: !(f (BVType 64)) -> X86PrimFn f (BVType 80)
  -- ^ This returns a 80-bit value where the high 16-bits are all
  -- 1s, and the low 64-bits are the given register.
  X86IDiv :: !(RepValSize w)
          -> !(f (BVType (w+w)))
          -> !(f (BVType w))
          -> X86PrimFn f (BVType w)
  -- ^ This performs a signed quotient for idiv.
  -- It raises a #DE exception if the divisor is 0 or the result overflows.
  -- The stored result is truncated to zero.
  X86IRem :: !(RepValSize w)
          -> !(f (BVType (w+w)))
          -> !(f (BVType w))
          -> X86PrimFn f (BVType w)
  -- ^ This performs a signed remainder for idiv.
  -- It raises a #DE exception if the divisor is 0 or the quotient overflows.
  -- The stored result is truncated to zero.
  X86Div :: !(RepValSize w)
         -> !(f (BVType (w+w)))
         -> !(f (BVType w))
         -> X86PrimFn f (BVType w)
  -- ^ This performs a unsigned quotient for div.
  -- It raises a #DE exception if the divisor is 0 or the quotient overflows.
  X86Rem :: !(RepValSize w)
         -> !(f (BVType (w+w)))
         -> !(f (BVType w))
         -> X86PrimFn f (BVType w)
  -- ^ This performs an unsigned remainder for div.
  -- It raises a #DE exception if the divisor is 0 or the quotient overflows.

  UCOMIS :: !(UCOMType tp)
         -> !(f tp)
         -> !(f tp)
         -> X86PrimFn f (TupleType [BoolType, BoolType, BoolType])
  -- ^  This performs a comparison of two floating point values and returns three flags:
  --
  --  * ZF is for the zero-flag and true if the arguments are equal or either argument is a NaN.
  --
  --  * PF records the unordered flag and is true if either value is a NaN.
  --
  --  * CF is the carry flag, and true if the first floating point argument is less than
  --    second or either value is a NaN.
  --
  -- The order of the flags was chosen to be consistent with the Intel documentation for
  -- UCOMISD and UCOMISS.
  --
  -- The documentation is a bit unclear, but it appears this function implicitly depends
  -- on the MXCSR register and may signal if the invalid operation exception #I is
  -- not masked or the denomal exception #D if it is not masked.

-- | A single or double value for floating-point restricted to this types.
data UCOMType tp where
   UCOMSingle :: UCOMType (FloatType SingleFloat)
   UCOMDouble :: UCOMType (FloatType DoubleFloat)

instance HasRepr UCOMType TypeRepr where
  typeRepr UCOMSingle = knownType
  typeRepr UCOMDouble = knownType

instance HasRepr (X86PrimFn f) TypeRepr where
  typeRepr f =
    case f of
      EvenParity{}  -> knownType
      ReadLoc loc   -> typeRepr loc
      ReadFSBase    -> knownType
      ReadGSBase    -> knownType
      CPUID{}       -> knownType
      RDTSC{}       -> knownType
      XGetBV{}      -> knownType
      PShufb w _ _  -> BVTypeRepr (typeRepr w)
      MemCmp{}      -> knownType
      RepnzScas{}   -> knownType
      MMXExtend{}   -> knownType
      X86IDiv w _ _ -> typeRepr (repValSizeMemRepr w)
      X86IRem w _ _ -> typeRepr (repValSizeMemRepr w)
      X86Div  w _ _ -> typeRepr (repValSizeMemRepr w)
      X86Rem  w _ _ -> typeRepr (repValSizeMemRepr w)
      UCOMIS _ _ _  -> knownType

instance FunctorFC X86PrimFn where
  fmapFC = fmapFCDefault

instance FoldableFC X86PrimFn where
  foldMapFC = foldMapFCDefault

instance TraversableFC X86PrimFn where
  traverseFC go f =
    case f of
      EvenParity x -> EvenParity <$> go x
      ReadLoc l  -> pure (ReadLoc l)
      ReadFSBase -> pure ReadFSBase
      ReadGSBase -> pure ReadGSBase
      CPUID v    -> CPUID <$> go v
      RDTSC      -> pure RDTSC
      XGetBV v   -> XGetBV <$> go v
      PShufb w x y -> PShufb w <$> go x <*> go y
      MemCmp sz cnt src dest rev ->
        MemCmp sz <$> go cnt <*> go src <*> go dest <*> go rev
      RepnzScas sz val buf cnt ->
        RepnzScas sz <$> go val <*> go buf <*> go cnt
      MMXExtend v -> MMXExtend <$> go v
      X86IDiv w n d -> X86IDiv w <$> go n <*> go d
      X86IRem w n d -> X86IRem w <$> go n <*> go d
      X86Div  w n d -> X86Div  w <$> go n <*> go d
      X86Rem  w n d -> X86Rem  w <$> go n <*> go d
      UCOMIS tp x y -> UCOMIS tp <$> go x <*> go y

instance IsArchFn X86PrimFn where
  ppArchFn pp f =
    case f of
      EvenParity x -> sexprA "even_parity" [ pp x ]
      ReadLoc loc -> pure $ pretty loc
      ReadFSBase  -> pure $ text "fs.base"
      ReadGSBase  -> pure $ text "gs.base"
      CPUID code  -> sexprA "cpuid" [ pp code ]
      RDTSC       -> pure $ text "rdtsc"
      XGetBV code -> sexprA "xgetbv" [ pp code ]
      PShufb _ x s -> sexprA "pshufb" [ pp x, pp s ]
      MemCmp sz cnt src dest rev -> sexprA "memcmp" args
        where args = [pure (pretty sz), pp cnt, pp dest, pp src, pp rev]
      RepnzScas _ val buf cnt  -> sexprA "first_byte_offset" args
        where args = [pp val, pp buf, pp cnt]
      MMXExtend e -> sexprA "mmx_extend" [ pp e ]
      X86IDiv w n d -> sexprA "idiv" [ pure (text $ show $ typeWidth $ repValSizeMemRepr w), pp n, pp d ]
      X86IRem w n d -> sexprA "irem" [ pure (text $ show $ typeWidth $ repValSizeMemRepr w), pp n, pp d ]
      X86Div  w n d -> sexprA "div"  [ pure (text $ show $ typeWidth $ repValSizeMemRepr w), pp n, pp d ]
      X86Rem  w n d -> sexprA "rem"  [ pure (text $ show $ typeWidth $ repValSizeMemRepr w), pp n, pp d ]
      UCOMIS  _ x y -> sexprA "ucomis" [ pp x, pp y ]

-- | This returns true if evaluating the primitive function implicitly
-- changes the processor state in some way.
x86PrimFnHasSideEffects :: X86PrimFn f tp -> Bool
x86PrimFnHasSideEffects f =
  case f of
    EvenParity{} -> False
    ReadLoc{}    -> False
    ReadFSBase   -> False
    ReadGSBase   -> False
    CPUID{}      -> False
    RDTSC        -> False
    XGetBV{}     -> False
    PShufb{}     -> False
    MemCmp{}     -> False
    RepnzScas{}  -> True
    MMXExtend{}  -> False
    X86IDiv{}    -> True -- To be conservative we treat the divide errors as side effects.
    X86IRem{}    -> True -- /\ ..
    X86Div{}     -> True -- /\ ..
    X86Rem{}     -> True -- /\ ..
    UCOMIS{}     -> True

------------------------------------------------------------------------
-- X86Stmt

-- | An X86 specific statement.
data X86Stmt (v :: Type -> *)
   = forall tp .
     WriteLoc !(X86PrimLoc tp) !(v tp)
   | StoreX87Control !(v (BVType 64))
     -- ^ Store the X87 control register in the given location.
   | MemCopy !Integer
             !(v (BVType 64))
             !(v (BVType 64))
             !(v (BVType 64))
             !(v BoolType)
     -- ^ Copy a region of memory from a source buffer to a destination buffer.
     --
     -- In an expression @MemCopy bc v src dest dir@
     -- * @bc@ is the number of bytes to copy at a time (1,2,4,8)
     -- * @v@ is the number of values to move.
     -- * @src@ is the start of source buffer.
     -- * @dest@ is the start of destination buffer.
     -- * @dir@ is a flag that indicates whether direction of move:
     --   * 'True' means we should decrement buffer pointers after each copy.
     --   * 'False' means we should increment the buffer pointers after each copy.
   | forall n .
     MemSet !(v (BVType 64))
            -- /\ Number of values to assign
            !(v (BVType n))
            -- /\ Value to assign
            !(v (BVType 64))
            -- /\ Address to start assigning from.
            !(v BoolType)
            -- /\ Direction flag

instance FunctorF X86Stmt where
  fmapF = fmapFDefault

instance FoldableF X86Stmt where
  foldMapF = foldMapFDefault

instance TraversableF X86Stmt where
  traverseF go stmt =
    case stmt of
      WriteLoc loc v    -> WriteLoc loc <$> go v
      StoreX87Control v -> StoreX87Control <$> go v
      MemCopy bc v src dest dir -> MemCopy bc <$> go v <*> go src <*> go dest <*> go dir
      MemSet  v src dest dir    -> MemSet <$> go v <*> go src <*> go dest <*> go dir

instance IsArchStmt X86Stmt where
  ppArchStmt pp stmt =
    case stmt of
      WriteLoc loc rhs -> pretty loc <+> text ":=" <+> pp rhs
      StoreX87Control addr -> pp addr <+> text ":= x87_control"
      MemCopy sz cnt src dest rev ->
          text "memcopy" <+> parens (hcat $ punctuate comma args)
        where args = [pretty sz, pp cnt, pp src, pp dest, pp rev]
      MemSet cnt val dest d ->
          text "memset" <+> parens (hcat $ punctuate comma args)
        where args = [pp cnt, pp val, pp dest, pp d]

------------------------------------------------------------------------
-- X86_64

data X86_64

type instance ArchReg  X86_64 = X86Reg
type instance ArchFn   X86_64 = X86PrimFn
type instance ArchStmt X86_64 = X86Stmt
type instance ArchTermStmt X86_64 = X86TermStmt

rewriteX86PrimFn :: X86PrimFn (Value X86_64 src) tp
                 -> Rewriter X86_64 s src tgt (Value X86_64 tgt tp)
rewriteX86PrimFn f =
  case f of
    EvenParity (BVValue _ xv) -> do
      let go 8 r = r
          go i r = go (i+1) $! (xv `testBit` i /= r)
      pure $ BoolValue (go 0 True)
    MMXExtend e -> do
      tgtExpr <- rewriteValue e
      case tgtExpr of
        BVValue _ i -> do
          pure $ BVValue (knownNat :: NatRepr 80) $ 0xffff `shiftL` 64 .|. i
        _ -> evalRewrittenArchFn (MMXExtend tgtExpr)
    _ -> do
      evalRewrittenArchFn =<< traverseFC rewriteValue f

rewriteX86Stmt :: X86Stmt (Value X86_64 src) -> Rewriter X86_64 s src tgt ()
rewriteX86Stmt f = do
  s <- traverseF rewriteValue f
  appendRewrittenArchStmt s

rewriteX86TermStmt :: X86TermStmt src -> Rewriter X86_64 s src tgt (X86TermStmt tgt)
rewriteX86TermStmt f =
  case f of
    X86Syscall -> pure X86Syscall
