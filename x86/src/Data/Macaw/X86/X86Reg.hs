{-
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This defines a type for representing what Reopt considers registers on
X86_64.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.X86.X86Reg
  ( ProgramCounter
  , GP
  , Flag
  , Segment
  , Control
  , Debug
  , X87_FPU
  , X87_Status
  , X87_Top
  , X87_Tag
  , X87_ControlMask
  , X87_Control
  , XMM
  , YMM
  , ZMM

    -- * X86Reg
  , X86Reg(..)

  , BitConversion(..)
  , BitPacking(..)
--  , registerWidth

  , x87StatusNames
    -- * General purpose registers
  , pattern RAX
  , pattern RBX
  , pattern RCX
  , pattern RDX
  , pattern RSI
  , pattern RDI
  , pattern RSP
  , pattern RBP
  , pattern R8
  , pattern R9
  , pattern R10
  , pattern R11
  , pattern R12
  , pattern R13
  , pattern R14
  , pattern R15
    -- * X86 Flags
  , pattern CF
  , pattern PF
  , pattern AF
  , pattern ZF
  , pattern SF
  , pattern TF
  , pattern IF
  , pattern DF
  , pattern OF
    -- * X87 status flags
  , pattern X87_IE
  , pattern X87_DE
  , pattern X87_ZE
  , pattern X87_OE
  , pattern X87_UE
  , pattern X87_PE
  , pattern X87_EF
  , pattern X87_ES
  , pattern X87_C0
  , pattern X87_C1
  , pattern X87_C2
  , pattern X87_C3
    -- * Large registers
  , pattern ZMM

    -- * Register lists
  , gpRegList
  , flagRegList
  , zmmRegList
  , x87FPURegList
  , x86StateRegs
  , x86CalleeSavedRegs
  , x86GPPArgumentRegs
  , x86ArgumentRegs
  , x86FloatArgumentRegs
  , x86ResultRegs
  , x86FloatResultRegs
  ) where

import           Data.Word(Word8)
import           Data.Macaw.CFG (RegAddrWidth, RegisterInfo(..), PrettyF(..))
import           Data.Macaw.Types
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Flexdis86 as F
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import qualified Data.Macaw.X86.X86Flag as R

-- Widths of common types
type ProgramCounter  = BVType 64
type GP              = BVType 64
type Flag            = BoolType
type Segment         = BVType 16
type Control         = BVType 64
type Debug           = BVType 64
type X87_FPU         = BVType 80
type X87_Status      = BoolType
type X87_Top         = BVType 3
type X87_Tag         = BVType 2
type X87_ControlMask = BVType 1
type X87_Control     = BVType 2
type XMM             = BVType 128
type YMM             = BVType 256
type ZMM             = BVType 512

------------------------------------------------------------------------
-- X86Reg

-- The datatype for x86 registers.
data X86Reg tp
   = (tp ~ BVType 64)  => X86_IP
     -- | One of 16 general purpose registers
   | (tp ~ BVType 64)  => X86_GP {-# UNPACK #-} !F.Reg64
     -- | One of 32 initial flag registers.
   | (tp ~ BoolType)   => X86_FlagReg {-# UNPACK #-} !R.X86Flag
     -- | One of 16 x87 status registers
   | (tp ~ BoolType)   => X87_StatusReg {-# UNPACK #-} !Int
     -- | X87 tag register.
   | (tp ~ BVType 3)   => X87_TopReg
     -- X87 tag register.
   | (tp ~ BVType 2)   => X87_TagReg {-# UNPACK #-} !Int
      -- One of 8 fpu/mmx registers.
   | (tp ~ BVType 80)  => X87_FPUReg {-#UNPACK #-} !F.MMXReg
     -- AVX2 has 32 512-bit registers.
   | (tp ~ BVType 512) => X86_ZMMReg !Word8


instance Show (X86Reg tp) where
  show X86_IP          = "rip"
  show (X86_GP r)      = show r
  show (X86_FlagReg r) = show r
  show (X87_StatusReg r) = nm
    where Just nm = x87StatusNames V.!? r
  show X87_TopReg      = "x87top"
  show (X87_TagReg n)  = "tag" ++ show n
  show (X87_FPUReg r)  = show r
  show (X86_ZMMReg r)  = "zmm" ++ show r

instance ShowF X86Reg where
  showF = show

instance PrettyF X86Reg where
  prettyF = text . show

instance TestEquality X86Reg where
  testEquality x y = orderingIsEqual (compareF x y)
    where
      -- FIXME: copied from Representation.hs, move
      orderingIsEqual :: OrderingF (x :: k) (y :: k) -> Maybe (x :~: y)
      orderingIsEqual o =
        case o of
         LTF -> Nothing
         EQF -> Just Refl
         GTF -> Nothing

instance Eq (X86Reg tp) where
  r == r'
    | Just _ <- testEquality r r' = True
    | otherwise = False

instance OrdF X86Reg where
  compareF X86_IP            X86_IP            = EQF
  compareF X86_IP            _                 = LTF
  compareF _                 X86_IP            = GTF

  compareF (X86_GP n)        (X86_GP n')        = fromOrdering (compare n n')
  compareF X86_GP{}           _                 = LTF
  compareF _                 X86_GP{}           = GTF

  compareF (X86_FlagReg n)   (X86_FlagReg n')   = fromOrdering (compare n n')
  compareF X86_FlagReg{}         _              = LTF
  compareF _                 X86_FlagReg{}      = GTF

  compareF (X87_StatusReg n) (X87_StatusReg n') = fromOrdering (compare n n')
  compareF X87_StatusReg{}    _                 = LTF
  compareF _                 X87_StatusReg{}    = GTF

  compareF X87_TopReg         X87_TopReg        = EQF
  compareF X87_TopReg         _                 = LTF
  compareF _                 X87_TopReg         = GTF

  compareF (X87_TagReg n)     (X87_TagReg n')     = fromOrdering (compare n n')
  compareF X87_TagReg{}       _                  = LTF
  compareF _                 X87_TagReg{}        = GTF

  compareF (X87_FPUReg n)     (X87_FPUReg n')    = fromOrdering (compare n n')
  compareF X87_FPUReg{}       _                  = LTF
  compareF _                 X87_FPUReg{}        = GTF

  compareF (X86_ZMMReg n)        (X86_ZMMReg n') = fromOrdering (compare n n')

instance Ord (X86Reg cl) where
  a `compare` b = case a `compareF` b of
    GTF -> GT
    EQF -> EQ
    LTF -> LT

instance Hashable (X86Reg tp) where
  hashWithSalt s r =
    case r of
      X86_IP           -> s `hashWithSalt` (0::Int)
      X86_GP i         -> s `hashWithSalt` (1::Int) `hashWithSalt` F.reg64No i
      X86_FlagReg i    -> s `hashWithSalt` (2::Int) `hashWithSalt` R.flagIndex i
      X87_StatusReg i  -> s `hashWithSalt` (3::Int) `hashWithSalt` i
      X87_TopReg       -> s `hashWithSalt` (4::Int)
      X87_TagReg i     -> s `hashWithSalt` (5::Int) `hashWithSalt` i
      X87_FPUReg i     -> s `hashWithSalt` (6::Int) `hashWithSalt` F.mmxRegNo i
      X86_ZMMReg i     -> s `hashWithSalt` (7::Int) `hashWithSalt` i

instance HashableF X86Reg where
  hashWithSaltF = hashWithSalt

instance HasRepr X86Reg TypeRepr where
  typeRepr r =
    case r of
      X86_IP           -> knownRepr
      X86_GP{}         -> knownRepr
      X86_FlagReg{}    -> knownRepr
      X87_StatusReg{}  -> knownRepr
      X87_TopReg       -> knownRepr
      X87_TagReg{}     -> knownRepr
      X87_FPUReg{}     -> knownRepr
      X86_ZMMReg{}     -> knownRepr

------------------------------------------------------------------------
-- Exported constructors and their conversion to words

-- | A description of how a sub-word may be extracted from a word. If a bit isn't
-- constant or from a register it is reserved.
data BitConversion n = forall m n'. (1 <= n', n' <= n)
                       => RegisterBit (X86Reg (BVType n')) (NatRepr m)
                     | forall m. (m + 1 <= n) => ConstantBit Bool (NatRepr m)

-- | A description of how a particular status word is packed/unpacked into sub-bits
data BitPacking (n :: Nat) = BitPacking (NatRepr n) [BitConversion n]

------------------------------------------------------------------------
-- General purpose register aliases.

-- NOTE: the patterns are written in this funny style, so that
-- when we pattern match we learn the right kind of type info. Argh.

pattern RAX :: () => (t ~ GP) => X86Reg t
pattern RAX = X86_GP F.RAX

pattern RBX :: () => (t ~ GP) => X86Reg t
pattern RBX = X86_GP F.RBX

pattern RCX :: () => (t ~ GP) => X86Reg t
pattern RCX = X86_GP F.RCX

pattern RDX :: () => (t ~ GP) => X86Reg t
pattern RDX = X86_GP F.RDX

pattern RSI :: () => (t ~ GP) => X86Reg t
pattern RSI = X86_GP F.RSI

pattern RDI :: () => (t ~ GP) => X86Reg t
pattern RDI = X86_GP F.RDI

pattern RSP :: () => (t ~ GP) => X86Reg t
pattern RSP = X86_GP F.RSP

pattern RBP :: () => (t ~ GP) => X86Reg t
pattern RBP = X86_GP F.RBP

pattern R8  :: () => (t ~ GP) => X86Reg t
pattern R8  = X86_GP F.R8

pattern R9  :: () => (t ~ GP) => X86Reg t
pattern R9  = X86_GP F.R9

pattern R10 :: () => (t ~ GP) => X86Reg t
pattern R10 = X86_GP F.R10

pattern R11 :: () => (t ~ GP) => X86Reg t
pattern R11 = X86_GP F.R11

pattern R12 :: () => (t ~ GP) => X86Reg t
pattern R12 = X86_GP F.R12

pattern R13 :: () => (t ~ GP) => X86Reg t
pattern R13 = X86_GP F.R13

pattern R14 :: () => (t ~ GP) => X86Reg t
pattern R14 = X86_GP F.R14

pattern R15 :: () => (t ~ GP) => X86Reg t
pattern R15 = X86_GP F.R15

pattern CF :: () => (t ~ BoolType) => X86Reg t
pattern CF = X86_FlagReg R.CF

pattern PF :: () => (t ~ BoolType) => X86Reg t
pattern PF = X86_FlagReg R.PF

pattern AF :: () => (t ~ BoolType) => X86Reg t
pattern AF = X86_FlagReg R.AF

pattern ZF :: () => (t ~ BoolType) => X86Reg t
pattern ZF = X86_FlagReg R.ZF

pattern SF :: () => (t ~ BoolType) => X86Reg t
pattern SF = X86_FlagReg R.SF

pattern TF :: () => (t ~ BoolType) => X86Reg t
pattern TF = X86_FlagReg R.TF

pattern IF :: () => (t ~ BoolType) => X86Reg t
pattern IF = X86_FlagReg R.IF

pattern DF :: () => (t ~ BoolType) => X86Reg t
pattern DF = X86_FlagReg R.DF

pattern OF :: () => (t ~ BoolType) => X86Reg t
pattern OF = X86_FlagReg R.OF

-- | x87 flags
pattern X87_IE :: () => (t ~ X87_Status) => X86Reg t
pattern X87_IE = X87_StatusReg 0

pattern X87_DE :: () => (t ~ X87_Status) => X86Reg t
pattern X87_DE = X87_StatusReg 1

pattern X87_ZE :: () => (t ~ X87_Status) => X86Reg t
pattern X87_ZE = X87_StatusReg 2

pattern X87_OE :: () => (t ~ X87_Status) => X86Reg t
pattern X87_OE = X87_StatusReg 3

pattern X87_UE :: () => (t ~ X87_Status) => X86Reg t
pattern X87_UE = X87_StatusReg 4

pattern X87_PE :: () => (t ~ X87_Status) => X86Reg t
pattern X87_PE = X87_StatusReg 5

pattern X87_EF :: () => (t ~ X87_Status) => X86Reg t
pattern X87_EF = X87_StatusReg 6

pattern X87_ES :: () => (t ~ X87_Status) => X86Reg t
pattern X87_ES = X87_StatusReg 7

pattern X87_C0 :: () => (t ~ X87_Status) => X86Reg t
pattern X87_C0 = X87_StatusReg 8

pattern X87_C1 :: () => (t ~ X87_Status) => X86Reg t
pattern X87_C1 = X87_StatusReg 9

pattern X87_C2 :: () => (t ~ X87_Status) => X86Reg t
pattern X87_C2 = X87_StatusReg 10

pattern X87_C3 :: () => (t ~ X87_Status) => X86Reg t
pattern X87_C3 = X87_StatusReg 14

pattern ZMM :: () => (t ~ ZMM) => Word8 -> X86Reg t
pattern ZMM w <- X86_ZMMReg w
  where ZMM w | w < 32 = X86_ZMMReg w
              | otherwise = error "There are only 32 ZMM registers."


x87StatusNames :: V.Vector String
x87StatusNames = V.fromList $
  [ "ie", "de", "ze", "oe",       "ue",       "pe",       "ef", "es"
  , "c0", "c1", "c2", "RESERVED_STATUS_11"
  , "RESERVED_STATUS_12", "RESERVED_STATUS_13", "c3", "RESERVED_STATUS_15"
  ]

------------------------------------------------------------------------
-- RegisterInfo instance

-- | The ABI defines these (http://www.x86-64.org/documentation/abi.pdf)
-- Syscalls clobber rcx and r11, but we don't really care about these anyway.
x86SyscallArgumentRegs :: [ X86Reg (BVType 64) ]
x86SyscallArgumentRegs = X86_GP <$> [ F.RDI, F.RSI, F.RDX, F.R10, F.R8, F.R9 ]

gpRegList :: [X86Reg (BVType 64)]
gpRegList = [X86_GP (F.Reg64 i) | i <- [0..15]]

flagRegList :: [X86Reg BoolType]
flagRegList = X86_FlagReg <$> R.flagList

x87StatusRegList :: [X86Reg BoolType]
x87StatusRegList = [X87_StatusReg i | i <- [0..15]]

x87TagRegList :: [X86Reg (BVType 2)]
x87TagRegList = [X87_TagReg i | i <- [0..7]]

x87FPURegList :: [X86Reg (BVType 80)]
x87FPURegList = [X87_FPUReg (F.mmxReg i) | i <- [0..7]]

zmmRegList :: [X86Reg (BVType 512)]
zmmRegList = [X86_ZMMReg i | i <- [0..31]]

-- | List of registers stored in X86State
x86StateRegs :: [Some X86Reg]
x86StateRegs
  =  [Some X86_IP]
  ++ (Some <$> gpRegList)
  ++ (Some <$> flagRegList)
  ++ (Some <$> x87StatusRegList)
  ++ [Some X87_TopReg]
  ++ (Some <$> x87TagRegList)
  ++ (Some <$> x87FPURegList)
  ++ (Some <$> zmmRegList)

type instance RegAddrWidth X86Reg = 64

instance RegisterInfo X86Reg where
  archRegs = x86StateRegs

  ip_reg = X86_IP
  sp_reg = RSP

  -- The register used to store system call numbers.
  syscall_num_reg = X86_GP F.RAX

  -- The ABI defines these (http://www.x86-64.org/documentation/abi.pdf)
  -- Syscalls clobber rcx and r11, but we don't really care about these
  -- anyway.
  syscallArgumentRegs = x86SyscallArgumentRegs


------------------------------------------------------------------------
-- Register information

-- | List of registers that a callee must save.
--
-- Note. This does not include the stack pointer (RSP) as that is
-- treated specially.
x86CalleeSavedRegs :: Set (Some X86Reg)
x86CalleeSavedRegs = Set.fromList $
  [ Some RBP
  , Some RBX
  , Some R12
  , Some R13
  , Some R14
  , Some R15
  , Some DF
  , Some X87_TopReg
  ]

-- | General purpose registers that may be needed for arguments according
-- to X86_64 ABI.
x86GPPArgumentRegs :: [F.Reg64]
x86GPPArgumentRegs = [F.RDI, F.RSI, F.RDX, F.RCX, F.R8, F.R9 ]

x86ArgumentRegs :: [X86Reg (BVType 64)]
x86ArgumentRegs = X86_GP <$> x86GPPArgumentRegs

x86FloatArgumentRegs :: [X86Reg (BVType 512)]
x86FloatArgumentRegs =  X86_ZMMReg <$> [0..7]

x86ResultRegs :: [X86Reg (BVType 64)]
x86ResultRegs = X86_GP <$> [ F.RAX, F.RDX ]

x86FloatResultRegs :: [X86Reg (BVType 512)]
x86FloatResultRegs = [ X86_ZMMReg 0 ]
