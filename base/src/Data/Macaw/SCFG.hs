{-|
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This exports the "simplifiable CFG" interface.  This CFG is designed
for simple optimizations including mem2reg
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.SCFG
  ( SCFG(..)
  , SCFGBlock(..)
  , CallingConvention
  , Stmt(..)
  , TermStmt(..)
  , Value(..)
  , AssignId(..)
  , BlockIndex(..)
  , module Data.Macaw.CFG.App
  ) where

{-
Concepts:

initial(r): This denotes the value in r when the function is called.


How will the algorithm work?

Example, suppose we have the following program:

simple.c:
  int add(int x, int y) {
      return x+y;
  }


gcc -c -o simple.o simple.c
ubuntu64:~% gobjdump -d simple.c


Then we run the following to get the disassembly:

> gcc -c -o simple.o simple.c && objdump -d simple.o

0000000000000000 <add>:
   0:	55                   	push   %rbp
   1:	48 89 e5             	mov    %rsp,%rbp
   4:	89 7d fc             	mov    %edi,-0x4(%rbp)
   7:	89 75 f8             	mov    %esi,-0x8(%rbp)
   a:	8b 55 fc             	mov    -0x4(%rbp),%edx
   d:	8b 45 f8             	mov    -0x8(%rbp),%eax
  10:	01 d0                	add    %edx,%eax
  12:	5d                   	pop    %rbp
  13:	c3                   	retq

// Reopt outputs the following:

function add @ segment1+0x0
segment1+0x0:
  # segment1+0x0: push   rbp
  r23 := (bv_add rsp_0 (0xfffffffffffffff8 :: [64]))
  write_mem r23 rbp_0
  # segment1+0x1: mov    rbp,rsp
  # segment1+0x4: mov    DWORD PTR [rbp-0x4],edi
  r24 := (trunc rdi_0 32)
  r25 := (bv_add rsp_0 (0xfffffffffffffff4 :: [64]))
  write_mem r25 r24
  # segment1+0x7: mov    DWORD PTR [rbp-0x8],esi
  r26 := (trunc rsi_0 32)
  r27 := (bv_add rsp_0 (0xfffffffffffffff0 :: [64]))
  write_mem r27 r26
  # segment1+0xa: mov    edx,DWORD PTR [rbp-0x4]
  r28 := read_mem r25 (bvle 4)
  r29 := (uext r28 64)
  # segment1+0xd: mov    eax,DWORD PTR [rbp-0x8]
  r30 := read_mem r27 (bvle 4)
  # segment1+0x10: add    eax,edx
  r32 := (sadc_overflows r30 r28 false)
  r33 := (trunc r30 4)
  r34 := (trunc r28 4)
  r35 := (uadc_overflows r33 r34 false)
  r36 := (uadc_overflows r30 r28 false)
  r37 := (bv_add r30 r28)
  r38 := (bv_slt r37 (0x0 :: [32]))
  r39 := (eq r37 (0x0 :: [32]))
  r40 := (trunc r37 8)
  r41 := (even_parity r40)
  r42 := (uext r37 64)
  # segment1+0x12: pop    rbp
  r43 := read_mem r23 (bvle 8)
  # segment1+0x13: ret
  r44 := read_mem rsp_0 (bvle 8)
  r45 := (bv_add rsp_0 (0x8 :: [64]))
  return
    { rip = r44
    , rax = r42
    , rdx = r29
    , rsp = r45
    , rbp = r43
    , cf = r36
    , pf = r41
    , af = r35
    , zf = r39
    , sf = r38
    , of = r32
    }

We would like the following:

````
function add @ segment1+0x0

Calling convention:
  stack grows down
  top of stack: rsp;

  dont care about writes in range [rsp-16..rsp].

  return_addr: *rsp;
  final(ip)  = read(initial_memory, rsp);
  final(rsp) = initial(rsp)+8;
  final(rbp) = initial(rbp);

segment1+0x0:
  r28 := (trunc rdi_0 32)
  r30 := (trunc rsi_0 32)
  r37 := (bv_add r30 r28)
  return
    { rax = (uext r37 64)
    , rdx = (uext r28 64)
    , af = (uadc_overflows (trunc r30 4) (trunc r28 4) false)
    , cf = (uadc_overflows r30 r28 false)
    , of = (sadc_overflows r30 r28 false)
    , pf = (even_parity (trunc r37 8))
    , zf = (eq r37 (0x0 :: [32]))
    , sf = (bv_slt r37 (0x0 :: [32]))
    }

Mask example
======


long mask(long c, long* a, long v) {
    long r = 0;
    for (long i = 0; i != c; ++c) {
	if (a[i] == v) {
	    r = 2*r + 1;
	} else {
	    r = 2*r;
	}
    }
    return r;
}

> gcc -c -o mask.o mask.c && objdump -d mask.o


0000000000000014 <mask>:
  14:	55                   	push   %rbp
  15:	48 89 e5             	mov    %rsp,%rbp
  18:	48 89 7d e8          	mov    %rdi,-0x18(%rbp)
  1c:	48 89 75 e0          	mov    %rsi,-0x20(%rbp)
  20:	48 89 55 d8          	mov    %rdx,-0x28(%rbp)
  24:	48 c7 45 f0 00 00 00 	movq   $0x0,-0x10(%rbp)
  2b:	00
  2c:	48 c7 45 f8 00 00 00 	movq   $0x0,-0x8(%rbp)
  33:	00
  34:	eb 36                	jmp    6c <mask+0x58>
  36:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  3a:	48 8d 14 c5 00 00 00 	lea    0x0(,%rax,8),%rdx
  41:	00
  42:	48 8b 45 e0          	mov    -0x20(%rbp),%rax
  46:	48 01 d0             	add    %rdx,%rax
  49:	48 8b 00             	mov    (%rax),%rax
  4c:	48 3b 45 d8          	cmp    -0x28(%rbp),%rax
  50:	75 11                	jne    63 <mask+0x4f>
  52:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  56:	48 01 c0             	add    %rax,%rax
  59:	48 83 c0 01          	add    $0x1,%rax
  5d:	48 89 45 f0          	mov    %rax,-0x10(%rbp)
  61:	eb 04                	jmp    67 <mask+0x53>
  63:	48 d1 65 f0          	shlq   -0x10(%rbp)
  67:	48 83 45 e8 01       	addq   $0x1,-0x18(%rbp)
  6c:	48 8b 45 f8          	mov    -0x8(%rbp),%rax
  70:	48 3b 45 e8          	cmp    -0x18(%rbp),%rax
  74:	75 c0                	jne    36 <mask+0x22>
  76:	48 8b 45 f0          	mov    -0x10(%rbp),%rax
  7a:	5d                   	pop    %rbp
  7b:	c3                   	retq


function mask @ segment1+0x14
segment1+0x14:
  # Predecessors = []
  r6 := (bv_add rsp_0 (0xfffffffffffffff8 :: [64]))
  r7 := (bv_add rsp_0 (0xffffffffffffffe0 :: [64]))
  r8 := (bv_add rsp_0 (0xffffffffffffffd8 :: [64]))
  r9 := (bv_add rsp_0 (0xffffffffffffffd0 :: [64]))
  r10 := (bv_add rsp_0 (0xffffffffffffffe8 :: [64]))
  r11 := (bv_add rsp_0 (0xfffffffffffffff0 :: [64]))
  write_mem r6 rbp_0
  write_mem r7 rdi_0
  write_mem r8 rsi_0
  write_mem r9 rdx_0
  write_mem r10 0x0 :: [64]
  write_mem r11 0x0 :: [64]
  jump segment1+0x6c
    { rip = segment1+0x6c
    , rsp = r6
    , rbp = r6
    , df = false
    , x87top = 0x7 :: [3]
    }
segment1+0x36:
  # Dominators: 0x6c

  #Predecessors = [0x6c]
  rbp_0 = phi [(0x14, rbp_0)]
  rsp_0 = phi [(0x14, rsp_0)]

  r662 := read_mem (rbp_0 -    8) (bvle 8)
  r665 := read_mem (rbp_0 - 0x20) (bvle 8)
  r678 := read_mem (rbp_0 - 0x28) (bvle 8)

  r663 := (bv_mul (0x8 :: [64]) r662)
  r671 := (bv_add r665 r663)
  r676 := read_mem r671 (bvle 8)
  r679 := (ssbb_overflows r676 r678 false)
  r680 := (trunc r676 4)
  r681 := (trunc r678 4)
  r682 := (bv_ult r680 r681)
  r683 := (bv_ult r676 r678)
  r684 := (bv_sub r676 r678)
  r685 := (bv_slt r684 (0x0 :: [64]))
  r686 := (eq r676 r678)
  r687 := (trunc r684 8)
  r688 := (even_parity r687)
  # segment1+0x50: jne    50+11
  r689 := (mux r686 (segment1+0x52) (segment1+0x63))
  ite r686
  {

    jump segment1+0x52
      { rip = segment1+0x52
      , rax = r676
      , rdx = r663
      , cf = r683
      , pf = r688
      , af = r682
      , zf = r686
      , sf = r685
      , df = false
      , of = r679
      , x87top = 0x7 :: [3]
      }
  }
  {

    jump segment1+0x63
      { rip = segment1+0x63
      , rax = r676
      , rdx = r663
      , cf = r683
      , pf = r688
      , af = r682
      , zf = r686
      , sf = r685
      , df = false
      , of = r679
      , x87top = 0x7 :: [3]
      }
  }
segment1+0x52:
  # Predecessors 0x36
  rbp_0 = phi [(0x36, rbp_0)]
  rsp_0 = phi [(0x36, rsp_0)]

  # segment1+0x52: mov    rax,QWORD PTR [rbp-0x10]
  r711 := read_mem (rbp_0 - 16) (bvle 8)
  # segment1+0x56: add    rax,rax
  r716 := (bv_add r711 r711)
  # segment1+0x59: add    rax,0x1
  r721 := (sadc_overflows r716 (0x1 :: [64]) false)
  r722 := (trunc r716 4)
  r723 := (uadc_overflows r722 (0x1 :: [4]) false)
  r724 := (uadc_overflows r716 (0x1 :: [64]) false)
  r725 := (bv_add r716 (0x1 :: [64]))
  r726 := (bv_slt r725 (0x0 :: [64]))
  r727 := (eq r716 (0xffffffffffffffff :: [64]))
  r728 := (trunc r725 8)
  r729 := (even_parity r728)
  # segment1+0x5d: mov    QWORD PTR [rbp-0x10],rax
  write_mem (rbp_0 - 0x10) r725
  # segment1+0x61: jmp    61+4
  jump segment1+0x67
    { rip = segment1+0x67
    , rax = r725
    , cf = r724
    , pf = r729
    , af = r723
    , zf = r727
    , sf = r726
    , df = false
    , of = r721
    , x87top = 0x7 :: [3]
    }
segment1+0x63:
  # Predecessors 0x36
  rbp_0 = phi [(0x14, rbp_0)]
  rsp_0 = phi [(0x14, rsp_0)]

  # segment1+0x63: shl    QWORD PTR [rbp-0x10],1
  r743 := read_mem (rbp_0 - 0x10) (bvle 8)
  r744 := undef :: [bool]
  r746 := (bv_slt r743 (0x0 :: [64]))
  r747 := (bv_slt r743 (0x0 :: [64]))
  r748 := (bv_shl r743 (0x1 :: [64]))
  r749 := (bv_slt r748 (0x0 :: [64]))
  r750 := (eq r748 (0x0 :: [64]))
  r751 := (trunc r748 8)
  r752 := (even_parity r751)
  write_mem (rbp_0 - 0x10) r748
  jump segment1+0x67
    { rip = segment1+0x67
    , cf = r747
    , pf = r752
    , af = r744
    , zf = r750
    , sf = r749
    , df = false
    , of = r746
    , x87top = 0x7 :: [3]
    }
segment1+0x67:
  # Predecessors 0x52, 0x63
  rbp_0 = phi [(0x14, rbp_0)]
  rsp_0 = phi [(0x14, rsp_0)]

  # segment1+0x67: add    QWORD PTR [rbp-0x18],0x1
  r591 := (bv_add rbp_0 (0xffffffffffffffe8 :: [64]))
  r592 := read_mem r591 (bvle 8)
  r593 := (sadc_overflows r592 (0x1 :: [64]) false)
  r594 := (trunc r592 4)
  r595 := (uadc_overflows r594 (0x1 :: [4]) false)
  r596 := (uadc_overflows r592 (0x1 :: [64]) false)
  r597 := (bv_add r592 (0x1 :: [64]))
  r598 := (bv_slt r597 (0x0 :: [64]))
  r599 := (eq r592 (0xffffffffffffffff :: [64]))
  r600 := (trunc r597 8)
  r601 := (even_parity r600)
  write_mem r591 r597
  jump segment1+0x6c
    { rip = segment1+0x6c
    , cf = r596
    , pf = r601
    , af = r595
    , zf = r599
    , sf = r598
    , df = false
    , of = r593
    , x87top = 0x7 :: [3]
    }
segment1+0x6c:
  # Predecessors 0x14 0x67
  rbp_0 = phi [(0x14, (rsp_0 - 8))]
  rsp_0 = phi [(0x14, (rsp_0 - 8))]


  r618 := read_mem (rbp_0 -    8) (bvle 8)
  r620 := read_mem (rbp_0 - 0x18) (bvle 8)
  r621 := (ssbb_overflows r618 r620 false)
  r622 := (trunc r618 4)
  r623 := (trunc r620 4)
  r624 := (bv_ult r622 r623)
  r625 := (bv_ult r618 r620)
  r626 := (bv_sub r618 r620)
  r627 := (bv_slt r626 (0x0 :: [64]))
  r628 := (eq r618 r620)
  r629 := (trunc r626 8)
  r630 := (even_parity r629)
  # segment1+0x74: jne    74+-40
  r631 := (mux r628 (segment1+0x76) (segment1+0x36))
  ite r628
  {

    jump segment1+0x76
      { rip = segment1+0x76
      , rax = r618
      , cf = r625
      , pf = r630
      , af = r624
      , zf = r628
      , sf = r627
      , df = false
      , of = r621
      , x87top = 0x7 :: [3]
      }
  }
  {

    jump segment1+0x36
      { rip = segment1+0x36
      , rax = r618
      , cf = r625
      , pf = r630
      , af = r624
      , zf = r628
      , sf = r627
      , df = false
      , of = r621
      , x87top = 0x7 :: [3]
      }
  }
segment1+0x76:
  # Predecessors 0x6c
  rbp_0 = phi [(0x14, (initial(rsp) - 8)]
  rsp_0 = phi [(0x14, (initial(rsp) - 8)]
  # Detect *(0x14, rsp_0) = return_addr


  r761 := read_mem (initial(rsp) - 0x18) (bvle 8)
  r762 := read_mem rsp_0 (bvle 8)
  r764 := read_mem (rsp_0 + 8) (bvle 8)
  return
    { rip = r764
    , rax = r761
    , rsp = initial(rsp) + 0x8
    , rbp = r762
    , df = false
    , x87top = 0x7 :: [3]
    }

0x14 -> 0x6c
0x6c -> 0x76 | 0x36
0x76 -> return
0x36 -> 0x52 | 0x63
0x52 -> 0x67
0x63 -> 0x67
0x67 -> 0x6c


0x14 -> 0x6c -> (0x36 -> (0x52|0x63|0x67))
             -> 0x76




0x6c -> 0x36
0x36 -> 0x52 | 0x63

========================================================================
== Implementation


First goal:
- Generate a ordering over the functions:

- f <= g if call @g appears inside a block of f.
- f <= g if there exists an h such that call g(f, ...)


Stack:

  Partial map from index to (BlockId,StmtIndex,Value) tuples.

Concepts


Build a dominator tree

-}


import           Data.Macaw.CFG.AssignRhs
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core (CValue(..))
import           Data.Macaw.Memory (AddrWidthRepr(..))
import           Data.Macaw.Types

import           Data.BinarySymbols
import           Data.ByteString.Char8 as BSC
import           Data.Map.Strict (Map)
import           Data.Parameterized.Map (MapF)
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Word
import           GHC.TypeLits

newtype BlockIndex = BlockIndex Word64

newtype AssignId ids (tp::Type) = AssignId (Nonce ids tp)

data Value arch ids tp where
  Const :: !(CValue arch tp) -> Value arch ids tp
  -- | Value from an assignment statement.
  AssignedValue :: !(AssignId ids tp)
                -> Value arch ids tp

type BVValue arch ids w = Value arch ids (BVType w)

type ArchAddrValue arch ids = BVValue arch ids (ArchAddrWidth arch)

-- | A statement in our control flow graph language.
data Stmt arch ids where
  AssignStmt :: !(AssignId ids tp)
             -> !(AssignRhs arch (Value arch ids) tp)
             -> Stmt arch ids
  -- | This denotes a write to memory, and consists of an address to write to, a `MemRepr` defining
  -- how the value should be stored in memory, and the value to be written.
  WriteMem :: !(ArchAddrValue arch ids)
           -> !(MemRepr tp)
           -> !(Value arch ids tp)
           -> Stmt arch ids
  -- | The start of an instruction
  --
  -- The information includes the offset relative to the start of the block and the
  -- disassembler output if available (or empty string if unavailable)
  InstructionStart :: !(ArchAddrWord arch)
                   -> !Text
                   -> Stmt arch ids
  -- | A user-level comment
  Comment :: !Text -> Stmt arch ids
  -- | Execute an architecture specific statement
  ExecArchStmt :: !(ArchStmt arch (Value arch ids)) -> Stmt arch ids
  -- /\ A call statement.
  --  RegCall :: !(RegState (ArchReg arch) (Value arch ids))
  --          -> Stmt arch ids

-- | This is a calling convention that explains how the linear list of
-- arguments should be stored for the ABI.
type family CallingConvention arch

-- | This term statement is used to describe higher level expressions
-- of how block ending with a a FetchAndExecute statement should be
-- interpreted.
data TermStmt arch ids where
  -- | A call with the current register values and location to return to or 'Nothing'  if this is a tail call.
  TailCall :: !(CallingConvention arch)
           -> !(BVValue arch ids (ArchAddrWidth arch))
              -- /\ IP to call
           -> ![Some (Value arch ids)]
           -> TermStmt arch ids
  -- | A jump to an explicit address within a function.
  Jump :: !BlockIndex
       -> TermStmt arch ids
  -- | A lookup table that branches to one of a vector of addresses.
  --
  -- The value contains the index to jump to as an unsigned bitvector, and the
  -- possible addresses as a table.  If the index (when interpreted as
  -- an unsigned number) is larger than the number of entries in the vector, then the
  -- result is undefined.
  LookupTable :: !(BVValue arch ids (ArchAddrWidth arch))
              -> !(V.Vector BlockIndex)
              -> TermStmt arch ids
  -- | A return with the given registers.
  Return :: !(MapF (ArchReg arch) (Value arch ids))
         -> TermStmt arch ids
  -- | An if-then-else
  Ite :: !(Value arch ids BoolType)
      -> !BlockIndex
      -> !BlockIndex
      -> TermStmt arch ids
  -- | An architecture-specific statement with the registers prior to execution, and
  -- the given next control flow address.
  ArchTermStmt :: !(ArchTermStmt arch ids)
               -> !(MapF (ArchReg arch) (Value arch ids))
               -> !(MapF (ArchReg arch) (Value arch ids))
               -> !(Maybe BlockIndex)
               -> TermStmt arch ids


data SCFGBlock arch ids
   = SCFGBlock { blockAddr     :: !(ArchSegmentOff arch)
               , blockIndex    :: !BlockIndex
               , blockInputs   :: ![Some TypeRepr]
                 -- ^ Types of inputs to block.
               , blockStmt     :: ![Stmt arch ids]
               , blockTermStmt :: !(TermStmt arch ids)
               }

data SCFG arch ids
   = SCFG { cfgAddr :: !(ArchSegmentOff arch)
          , cfgName :: !BSC.ByteString
          , cfgBlocks :: !(Map (ArchSegmentOff arch, BlockIndex) (SCFGBlock arch ids))
          }
