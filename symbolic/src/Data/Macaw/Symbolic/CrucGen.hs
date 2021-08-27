{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the core operations for mapping from Reopt to Crucible.
-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Symbolic.CrucGen
  ( MacawSymbolicArchFunctions(..)
  , crucArchRegTypes
  , MacawExt
  , MacawExprExtension(..)
  , MacawOverflowOp(..)
  , MacawStmtExtension(..)
  , MacawFunctionArgs
  , MacawFunctionResult
  , ArchAddrCrucibleType
  , MacawCrucibleRegTypes
  , ArchRegStruct
  , MacawArchConstraints
  , MacawArchStmtExtension
    -- ** Operations for implementing new backends.
  , CrucGen
  , MacawMonad
  , runMacawMonad
  , addMacawBlock
  , mmFreshNonce
  , mmNonceGenerator
  , mmExecST
  , BlockLabelMap
  , addParsedBlock
  , valueToCrucible
  , evalArchStmt
  , MemSegmentMap
  , MacawCrucibleValue(..)
    -- * Additional exports
  , runCrucGen
  , setMachineRegs
  , addTermStmt
  , parsedBlockLabel
  , ArchAddrWidthRepr
  , addrWidthIsPos
  , getRegs
  , addMacawStmt
  , addMacawParsedTermStmt
  , addStmt
  , addExtraBlock
  , appAtom
  , toBits
  , fromBits
  , evalMacawStmt
  , getRegValue
  , bvLit
  , archAddrWidth
  , evalAtom
  , crucibleValue
  ) where

import           Control.Lens hiding (Empty, (:>))
import           Control.Monad.Except
import qualified Control.Monad.Fail as MF
import           Control.Monad.State.Strict
import qualified Data.BitVector.Sized as BV
import qualified Data.Foldable as F
import qualified Data.Kind as K
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Types as M
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as P
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce (Nonce, NonceGenerator, freshNonce)
import           Data.Parameterized.Pair
import qualified Data.Parameterized.TH.GADT as U
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.Proxy
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as Vec
import           Prettyprinter hiding (width)

import           What4.ProgramLoc as C
import qualified What4.Symbol as C
import qualified What4.Utils.StringLiteral as C

import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.Types as C

import qualified Lang.Crucible.LLVM.MemModel as MM

import           Data.Macaw.Symbolic.PersistentState


-- | The Crucible type of a register state
--
-- The registers are stored in an 'Ctx.Assignment' tagged with their Macaw
-- types; this is a conversion of those Macaw types into Crucible types.
type MacawCrucibleRegTypes (arch :: K.Type) = CtxToCrucibleType (ArchRegContext arch)

-- | The type of the register file in the symbolic simulator
--
-- At run time, this is an 'Ctx.Assignment' of registers (where each register
-- has a Crucible type, which is mapped via 'CtxToCrucibleType' from its Macaw
-- type).
type ArchRegStruct (arch :: K.Type) = C.StructType (MacawCrucibleRegTypes arch)

type ArchAddrCrucibleType arch = MM.LLVMPointerType (M.ArchAddrWidth arch)

-- | The type used for the argument list of every Macaw function translated into Crucible
--
-- In this translation, every function takes a single argument (hence the
-- single-element 'Ctx'): the full register file for the machine.
type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch

-- | The type used for the return value of every Macaw function translated into Crucible
--
-- Similarly, every function in the translation returns a complete register
-- state.  In this way, every function is a transformer over the register state
-- of the machine (and, implicitly, over the memory model, which is held in a
-- global variable kept in the simulator).
type MacawFunctionResult arch = ArchRegStruct arch

type ArchAddrWidthRepr arch = M.AddrWidthRepr (M.ArchAddrWidth arch)

-- | The type of the architecture-specific extension to the Macaw extension to Crucible
--
-- While 'MacawExt' is the Macaw-specific extension to Crucible to simulate
-- macaw programs, 'MacawExt' itself requires extensions for each
-- architecture-specific backend to support operations that are not natively
-- supported in Crucible.
--
-- The simplest examples are support for systems call instructions and other
-- instructions with effects not expressible as Crucible code.
type family MacawArchStmtExtension (arch :: K.Type) :: (C.CrucibleType -> K.Type) -> C.CrucibleType -> K.Type

type MacawArchConstraints arch =
  ( TraversableFC (MacawArchStmtExtension arch)
  , C.TypeApp (MacawArchStmtExtension arch)
  , C.PrettyApp (MacawArchStmtExtension arch)
  , M.MemWidth (M.RegAddrWidth (M.ArchReg arch))
  , M.PrettyF (M.ArchReg arch)
  )

------------------------------------------------------------------------
-- CrucPersistentState

-- | Architecture-specific information needed to translate from Macaw to Crucible
--
-- Note that the constructor for this type is exposed to allow for new
-- implementations of architecture-specific backends.  Most client code will not
-- need to construct (or inspect) values of this type.  Values of this type
-- should be obtained via the 'archFunctions' field of the 'ArchVals'.
data MacawSymbolicArchFunctions arch
  = MacawSymbolicArchFunctions
  { crucGenArchConstraints
    :: !(forall a . ((M.RegisterInfo (M.ArchReg arch), MacawArchConstraints arch) => a) -> a)
  , crucGenRegAssignment :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
    -- ^ Map from indices in the ArchRegContext to the associated register.
  , crucGenRegStructType :: !(C.TypeRepr (ArchRegStruct arch))
    -- ^ Type of structure with arch regs.  This can be computed from
    -- @crucGenRegAssignment@, but is cached here to save memory (A
    -- LOT of memory---TypeReprs were dominating the heap).
  , crucGenArchRegName :: !(forall tp . M.ArchReg arch tp -> C.SolverSymbol)
    -- ^ Provides a solver name to use for referring to register.
  , crucGenArchFn :: !(forall ids s tp
                         . M.ArchFn arch (M.Value arch ids) tp
                         -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp)))
     -- ^ Generate crucible for architecture-specific function.
  , crucGenArchStmt
    :: !(forall ids s . M.ArchStmt arch (M.Value arch ids)
                      -> CrucGen arch ids s ())
     -- ^ Generate crucible for architecture-specific statement.
  , crucGenArchTermStmt :: !(forall ids s
                               . M.ArchTermStmt arch ids
                               -> M.RegState (M.ArchReg arch) (M.Value arch ids)
                               -> CrucGen arch ids s ())
     -- ^ Generate crucible for architecture-specific terminal statement.
  }

crucGenAddrWidth :: MacawSymbolicArchFunctions arch -> ArchAddrWidthRepr arch
crucGenAddrWidth fns =
  crucGenArchConstraints fns $ M.addrWidthRepr Proxy

-- | Return types of registers in Crucible
crucArchRegTypes
  :: MacawSymbolicArchFunctions arch
  -> Assignment C.TypeRepr (MacawCrucibleRegTypes arch)
crucArchRegTypes arch_fns = case crucGenRegStructType arch_fns of
  C.StructRepr tps -> tps

------------------------------------------------------------------------
-- MacawExprExtension

-- | Different types of arithmetic overflow for the overflow test extension
-- expression ('MacawOverflows')
data MacawOverflowOp
   = Uadc
   -- ^ Unsigned add with carry
   | Sadc
   -- ^ Signed add with carry
   | Usbb
   -- ^ Unsigned subtract with borrow overflow
   | Ssbb
   -- ^ Signed subtract with borrow overflow
  deriving (Eq, Ord, Show)

type BVPtr a       = MM.LLVMPointerType (M.ArchAddrWidth a)

-- | The extra expressions required to extend Crucible to support simulating
-- Macaw programs
data MacawExprExtension (arch :: K.Type)
                        (f :: C.CrucibleType -> K.Type)
                        (tp :: C.CrucibleType) where
  -- | Test to see if a given operation ('MacawOverflowOp') overflows
  --
  -- The operation being tested for is the first operand.  The two operands of
  -- 'C.BVType' are the numeric operands.  The 'C.BoolType' operand is the carry
  -- in or borrow bit (depending on the operation)
  MacawOverflows :: (1 <= w)
                 => !MacawOverflowOp
                 -> !(NatRepr w)
                 -> !(f (C.BVType w))
                 -> !(f (C.BVType w))
                 -> !(f C.BoolType)
                 -> MacawExprExtension arch f C.BoolType

  -- | Treat an LLVM pointer as a bitvector
  PtrToBits
    :: (1 <= w)
    => !(NatRepr w)
    -> !(f (MM.LLVMPointerType w))
    -> MacawExprExtension arch f (C.BVType w)

  -- | Treat a bitvector as a pointer, which we can read from if it is a valid
  -- pointer.  The simulator will attempt the conversion with
  -- 'MM.llvmPointer_bv', which generates side conditions that will be tested by
  -- the solver.
  BitsToPtr
    :: (1 <= w)
    => !(NatRepr w)
    -> !(f (C.BVType w))
    -> MacawExprExtension arch f (MM.LLVMPointerType w)

  -- | A null pointer.
  MacawNullPtr
    :: !(ArchAddrWidthRepr arch)
    -> MacawExprExtension arch f (BVPtr arch)

  -- | Cast from one macaw value to another.
  MacawBitcast :: !(f (ToCrucibleType i))
               -> !(M.WidthEqProof i o)
               -> MacawExprExtension arch f (ToCrucibleType o)


instance C.PrettyApp (MacawExprExtension arch) where
  ppApp f a0 =
    case a0 of
      MacawOverflows o w x y c ->
        let mnem = "macawOverflows_" ++ show o ++ "_" ++ show w
         in sexpr mnem [f x, f y, f c]

      PtrToBits w x  -> sexpr ("ptr_to_bits_" ++ show w) [f x]
      BitsToPtr w x  -> sexpr ("bits_to_ptr_" ++ show w) [f x]

      MacawNullPtr _ -> sexpr "null_ptr" []
      MacawBitcast x p -> sexpr "bitcast" [f x, viaShow (M.widthEqTarget p)]

addrWidthIsPos :: M.AddrWidthRepr w -> LeqProof 1 w
addrWidthIsPos M.Addr32 = LeqProof
addrWidthIsPos M.Addr64 = LeqProof

instance C.TypeApp (MacawExprExtension arch) where
  appType x =
    case x of
      MacawOverflows {} -> C.knownRepr
      PtrToBits w _     -> C.BVRepr w
      BitsToPtr w _     -> MM.LLVMPointerRepr w
      MacawNullPtr w | LeqProof <- addrWidthIsPos w -> MM.LLVMPointerRepr (M.addrWidthNatRepr w)
      MacawBitcast _ p -> typeToCrucible (M.widthEqTarget p)

------------------------------------------------------------------------
-- MacawStmtExtension

-- | Extra extension statements required for Crucible to simulate Macaw programs
--
-- Note that the various @*Ptr@ operations below are statements, rather than
-- expressions, because they need to access memory (via the Crucible global
-- variable that contains the current memory model).
data MacawStmtExtension (arch :: K.Type)
                        (f    :: C.CrucibleType -> K.Type)
                        (tp   :: C.CrucibleType)
  where

  -- | Read from memory.
  --
  -- The 'M.MemRepr' describes the endianness and size of the read.
  MacawReadMem
    :: !(ArchAddrWidthRepr arch)
    -- Info about memory (endianness, size)
    -> !(M.MemRepr tp)
    -- Pointer to read from.
    -> !(f (ArchAddrCrucibleType arch))
    -> MacawStmtExtension arch f (ToCrucibleType tp)


  -- | Read from memory, if the condition is True.
  -- Otherwise, just return the given value.
  MacawCondReadMem
    :: !(ArchAddrWidthRepr arch)
    -- Info about memory (endianness, size)
    -> !(M.MemRepr tp)
    -- Condition
    -> !(f C.BoolType)
    -- Pointer to read from
    -> !(f (ArchAddrCrucibleType arch))
    -- Default value, returned if the condition is False.
    -> !(f (ToCrucibleType tp))
    -> MacawStmtExtension arch f (ToCrucibleType tp)

  -- | Write to memory
  MacawWriteMem
    :: !(ArchAddrWidthRepr arch)
    -> !(M.MemRepr tp)
    -> !(f (ArchAddrCrucibleType arch))
    -> !(f (ToCrucibleType tp))
    -> MacawStmtExtension arch f C.UnitType

  -- | Write to memory if condition is true
  MacawCondWriteMem
    :: !(ArchAddrWidthRepr arch)
    -> !(M.MemRepr tp)
    -- Condition
    -> !(f C.BoolType)
    -> !(f (ArchAddrCrucibleType arch))
    -> !(f (ToCrucibleType tp))
    -> MacawStmtExtension arch f C.UnitType

  -- | Convert a literal address (from Macaw) into a pointer in the LLVM memory model
  MacawGlobalPtr
    :: !(ArchAddrWidthRepr arch)
    -> !(M.MemAddr (M.ArchAddrWidth arch))
    -> MacawStmtExtension arch f (BVPtr arch)


  -- | Generate a fresh symbolic variable of the given type.
  MacawFreshSymbolic
    :: !(M.TypeRepr tp)
    -> MacawStmtExtension arch f (ToCrucibleType tp)

  -- | Look up the function handle for the current call given the entire register and memory state
  --
  -- This special statement takes an entire register state and computes the
  -- function that the program would jump to next.  Callers of the simulator
  -- provide the translation function.  Normally, this translation function will
  -- inspect the value of the instruction pointer and map that to a function
  -- address, possibly translating the function into a Crucible CFG on the fly.
  --
  -- This needs to be a statement to support the dynamic translation of the
  -- target CFG, and especially the registration of that CFG with the simulator.
  MacawLookupFunctionHandle
    :: !(Assignment C.TypeRepr (CtxToCrucibleType (ArchRegContext arch)))
    -> !(f (ArchRegStruct arch))
    -> MacawStmtExtension arch f (C.FunctionHandleType (Ctx.EmptyCtx Ctx.::> ArchRegStruct arch)
                                 (ArchRegStruct arch))

  -- | Look up a handle that models the effects of a system call
  --
  -- This is very similar to 'MacawLookupFunctionHandle', except that the
  -- interpretation uses a different lookup function (based on the syscall table
  -- for the OS/ABI).  The list of registers encodes the locations (besides
  -- memory) that the system call can update. The architecture-specific backends
  -- are responsible for ensuring that those updates are accounted for in the
  -- translation. It is handled this way because the translations of system
  -- calls are not really first-class in macaw, and thus they do not end blocks
  -- in a way that lets us update registers in the same way that the call
  -- sequence does.
  --
  -- Note that it is expected that the architecture-specific symbolic backends
  -- are expected to use this in their translation of their syscall arch functions.
  MacawLookupSyscallHandle
    :: !(Assignment C.TypeRepr atps)
    -> !(Assignment C.TypeRepr rtps)
    -> !(f (C.StructType atps))
    -> MacawStmtExtension arch f (C.FunctionHandleType atps (C.StructType rtps))

  -- | An architecture-specific machine instruction, for which an interpretation
  -- is required.  This interpretation must be provided by callers via the
  -- 'macawExtensions' function.
  MacawArchStmtExtension ::
    !(MacawArchStmtExtension arch f tp) ->
    MacawStmtExtension arch f tp

  -- | Metadata about updates to machine registers
  --
  -- After a machine instruction is finished executing, this statement records
  -- which Crucible values are logically in each machine register.
  MacawArchStateUpdate :: !(M.ArchMemAddr arch) ->
                          !(MapF.MapF (M.ArchReg arch) (MacawCrucibleValue f)) ->
                          MacawStmtExtension arch f C.UnitType

  -- | Record the start of the translation of a machine instruction
  --
  -- The instructions between a MacawInstructionStart and a MacawArchStateUpdate
  -- all correspond to a single machine instruction.  This metadata includes
  -- enough information to figure out exactly which machine instruction that is.
  MacawInstructionStart :: !(M.ArchSegmentOff arch)
                        -> !(M.ArchAddrWord arch)
                        -> !Text.Text
                        -> MacawStmtExtension arch f C.UnitType

  -- NOTE: The Ptr* operations below are statements and not expressions
  -- because they need to read the memory variable, to determine if their
  -- inputs are valid pointers.

  -- | Equality for pointer or bit-vector.
  PtrEq
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f C.BoolType

  -- | Unsigned comparison for pointer/bit-vector.
  PtrLeq
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f C.BoolType

  -- | Unsigned comparison for pointer/bit-vector.
  PtrLt
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f C.BoolType

  -- | Mux for pointers or bit-vectors.
  PtrMux
    :: !(ArchAddrWidthRepr arch)
    -> !(f C.BoolType)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f (BVPtr arch)

  -- | Add a pointer to a bit-vector, or two bit-vectors.
  PtrAdd
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f (BVPtr arch)

  -- | Subtract two pointers, two bit-vectors, or bit-vector from a pointer.
  PtrSub
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f (BVPtr arch)

  -- | And together two items.  Usually these are going to be bit-vectors,
  -- but sometimes we need to support "and"-ing a pointer with a constant,
  -- which happens when trying to align a pointer.
  PtrAnd
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f (BVPtr arch)

  PtrXor
    :: !(ArchAddrWidthRepr arch)
    -> !(f (BVPtr arch))
    -> !(f (BVPtr arch))
    -> MacawStmtExtension arch f (BVPtr arch)

instance TraversableFC (MacawArchStmtExtension arch)
      => FunctorFC (MacawStmtExtension arch) where
  fmapFC = fmapFCDefault

instance TraversableFC (MacawArchStmtExtension arch)
      => FoldableFC (MacawStmtExtension arch) where
  foldMapFC = foldMapFCDefault

sexpr :: String -> [Doc ann] -> Doc ann
sexpr s [] = pretty s
sexpr s l  = parens (pretty s <+> hsep l)

instance (C.PrettyApp (MacawArchStmtExtension arch),
          M.PrettyF (M.ArchReg arch),
          M.MemWidth (M.RegAddrWidth (M.ArchReg arch)))
      => C.PrettyApp (MacawStmtExtension arch) where
  ppApp :: forall f ann
        .  (forall (x :: C.CrucibleType) . f x -> Doc ann)
        -> (forall (x :: C.CrucibleType) . MacawStmtExtension arch f x -> Doc ann)
  ppApp f a0 =
    case a0 of
      MacawReadMem     _  r   a   -> sexpr "macawReadMem"      [pretty r, f a]
      MacawCondReadMem _  r c a d -> sexpr "macawCondReadMem"  [pretty r, f c, f a, f d ]
      MacawWriteMem     _ r   a v -> sexpr "macawWriteMem"     [pretty r, f a, f v]
      MacawCondWriteMem _ r c a v -> sexpr "macawCondWriteMem" [f c, pretty r, f a, f v]
      MacawGlobalPtr _ x -> sexpr "global" [ viaShow x ]

      MacawFreshSymbolic r -> sexpr "macawFreshSymbolic" [ viaShow r ]
      MacawLookupFunctionHandle _ regs -> sexpr "macawLookupFunctionHandle" [ f regs ]
      MacawLookupSyscallHandle _ _ regs -> sexpr "macawLookupSyscallHandle" [ f regs ]
      MacawArchStmtExtension a -> C.ppApp f a
      MacawArchStateUpdate addr m ->
        let prettyArchStateBinding :: forall tp . M.ArchReg arch tp -> MacawCrucibleValue f tp -> [Doc ann] -> [Doc ann]
            prettyArchStateBinding reg (MacawCrucibleValue val) acc =
              (M.prettyF reg <> " => " <> f val) : acc
        in sexpr "macawArchStateUpdate" [pretty addr, encloseSep lbrace rbrace semi (MapF.foldrWithKey prettyArchStateBinding [] m)]
      MacawInstructionStart baddr ioff t ->
        sexpr "macawInstructionStart" [ pretty baddr, pretty ioff, viaShow t ]
      PtrEq _ x y    -> sexpr "ptr_eq" [ f x, f y ]
      PtrLt _ x y    -> sexpr "ptr_lt" [ f x, f y ]
      PtrLeq _ x y   -> sexpr "ptr_leq" [ f x, f y ]
      PtrAdd _ x y   -> sexpr "ptr_add" [ f x, f y ]
      PtrSub _ x y   -> sexpr "ptr_sub" [ f x, f y ]

      PtrAnd _ x y   -> sexpr "ptr_and" [ f x, f y ]
      PtrXor _ x y   -> sexpr "ptr_xor" [ f x, f y ]
      PtrMux _ c x y -> sexpr "ptr_mux" [ f c, f x, f y ]


instance C.TypeApp (MacawArchStmtExtension arch)
      => C.TypeApp (MacawStmtExtension arch) where
  appType (MacawReadMem _ r _) = memReprToCrucible r
  appType (MacawCondReadMem _ r _ _ _) = memReprToCrucible r
  appType (MacawWriteMem _ _ _ _) = C.knownRepr
  appType MacawCondWriteMem{} = C.knownRepr
  appType (MacawGlobalPtr w _)
    | LeqProof <- addrWidthIsPos w = MM.LLVMPointerRepr (M.addrWidthNatRepr w)
  appType (MacawFreshSymbolic r) = typeToCrucible r
  appType (MacawLookupFunctionHandle regTypes _) =
    C.FunctionHandleRepr (Ctx.singleton (C.StructRepr regTypes)) (C.StructRepr regTypes)
  appType (MacawLookupSyscallHandle argTypes retType _) =
    C.FunctionHandleRepr argTypes (C.StructRepr retType)
  appType (MacawArchStmtExtension f) = C.appType f
  appType MacawArchStateUpdate {} = C.knownRepr
  appType MacawInstructionStart {} = C.knownRepr
  appType PtrEq {}            = C.knownRepr
  appType PtrLt {}            = C.knownRepr
  appType PtrLeq {}           = C.knownRepr
  appType (PtrAdd w _ _)   | LeqProof <- addrWidthIsPos w = MM.LLVMPointerRepr (M.addrWidthNatRepr w)
  appType (PtrAnd w _ _)   | LeqProof <- addrWidthIsPos w = MM.LLVMPointerRepr (M.addrWidthNatRepr w)
  appType (PtrSub w _ _)   | LeqProof <- addrWidthIsPos w = MM.LLVMPointerRepr (M.addrWidthNatRepr w)
  appType (PtrXor w _ _)   | LeqProof <- addrWidthIsPos w = MM.LLVMPointerRepr (M.addrWidthNatRepr w)
  appType (PtrMux w _ _ _) | LeqProof <- addrWidthIsPos w = MM.LLVMPointerRepr (M.addrWidthNatRepr w)

------------------------------------------------------------------------
-- MacawExt

-- | The Crucible extension used to represent Macaw-specific operations
data MacawExt (arch :: K.Type)

type instance C.ExprExtension (MacawExt arch) = MacawExprExtension arch
type instance C.StmtExtension (MacawExt arch) = MacawStmtExtension arch

instance MacawArchConstraints arch
      => C.IsSyntaxExtension (MacawExt arch)

-- | Map from indices of segments without a fixed base address to a
-- global variable storing the base address.
--
-- This uses a global variable so that we can do the translation, and then
-- decide where to locate it without requiring us to also pass the values
-- around arguments.
type MemSegmentMap w = Map M.RegionIndex (CR.GlobalVar (C.BVType w))

-- | State used for generating blocks
data CrucGenState arch ids s
   = CrucGenState
   { translateFns       :: !(MacawSymbolicArchFunctions arch)
   , crucRegIndexMap :: !(RegIndexMap arch)
     -- ^ Map from architecture register to Crucible/Macaw index pair.
   , crucPState      :: !(CrucPersistentState ids s)
     -- ^ State that persists across blocks.
   , crucRegisterReg :: !(CR.Reg s (ArchRegStruct arch))
   , macawPositionFn :: !(M.ArchAddrWord arch -> C.Position)
     -- ^ Map from offset to Crucible position.
   , blockLabel :: (CR.Label s)
     -- ^ Label for this block we are translating
   , codeOff    :: !(M.ArchAddrWord arch)
     -- ^ Offset
   , codePos    :: !C.Position
     -- ^ Position (cached from 'codeOff')
   , prevStmts  :: ![C.Posd (CR.Stmt (MacawExt arch) s)]
     -- ^ List of states in reverse order
   , toBitsCache :: !(MapF (PtrAtom s) (BVAtom s))
   , fromBitsCache :: !(MapF (BVAtom s) (PtrAtom s))
   , extraBlocks :: ![CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
     -- ^ Extra blocks created during construction, in reverse order of creation
   }

newtype PtrAtom s w = PtrAtom { getPtrAtom :: CR.Atom s (MM.LLVMPointerType w) }

instance TestEquality (PtrAtom s) where
  testEquality x y =
    testEquality (getPtrAtom x) (getPtrAtom y) <&> \Refl -> Refl

instance OrdF (PtrAtom s) where
  compareF x y =
    case compareF (getPtrAtom x) (getPtrAtom y) of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

newtype BVAtom s w = BVAtom { getBVAtom :: CR.Atom s (C.BVType w) }

instance TestEquality (BVAtom s) where
  testEquality x y =
    testEquality (getBVAtom x) (getBVAtom y) <&> \Refl -> Refl

instance OrdF (BVAtom s) where
  compareF x y =
    case compareF (getBVAtom x) (getBVAtom y) of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

crucPStateLens ::
  Lens' (CrucGenState arch ids s) (CrucPersistentState ids s)
crucPStateLens = lens crucPState (\s v -> s { crucPState = v })

toBitsCacheLens ::
  Lens' (CrucGenState arch ids s) (MapF (PtrAtom s) (BVAtom s))
toBitsCacheLens = lens toBitsCache (\s v -> s { toBitsCache = v })

fromBitsCacheLens ::
  Lens' (CrucGenState arch ids s) (MapF (BVAtom s) (PtrAtom s))
fromBitsCacheLens = lens fromBitsCache (\s v -> s { fromBitsCache = v })

assignValueMapLens ::
  Lens' (CrucPersistentState ids s)
              (MapF (M.AssignId ids) (MacawCrucibleValue (CR.Atom s)))
assignValueMapLens = lens assignValueMap (\s v -> s { assignValueMap = v })

type CrucGenRet arch ids s = (CrucGenState arch ids s, CR.TermStmt s (MacawFunctionResult arch))

-- | The Crucible generator monad
--
-- This monad provides an environment for constructing Crucible blocks from
-- Macaw blocks, including the translation of values while preserving sharing
-- and the construction of a control flow graph.
newtype CrucGen arch ids s r
   = CrucGen { unCrucGen
               :: CrucGenState arch ids s
                  -> (CrucGenState arch ids s
                      -> r
                      -> IO (CrucGenRet arch ids s))
                  -> IO (CrucGenRet arch ids s)
             }

instance Functor (CrucGen arch ids s) where
  {-# INLINE fmap #-}
  fmap f m = CrucGen $ \s0 cont -> unCrucGen m s0 $ \s1 v -> cont s1 (f v)

instance Applicative (CrucGen arch ids s) where
  {-# INLINE pure #-}
  pure !r = CrucGen $ \s cont -> cont s r
  {-# INLINE (<*>) #-}
  mf <*> ma = CrucGen $ \s0 cont -> unCrucGen mf s0
                      $ \s1 f -> unCrucGen ma s1
                      $ \s2 a -> cont s2 (f a)

instance Monad (CrucGen arch ids s) where
  {-# INLINE (>>=) #-}
  m >>= h = CrucGen $ \s0 cont -> unCrucGen m s0 $ \s1 r -> unCrucGen (h r) s1 cont
#if !(MIN_VERSION_base(4,13,0))
  fail = MF.fail
#endif

instance MF.MonadFail (CrucGen arch ids s) where
  fail e = CrucGen $ \_s _cont -> MF.fail e

instance MonadState (CrucGenState arch ids s) (CrucGen arch ids s) where
  get = CrucGen $ \s cont -> cont s s
  put s = CrucGen $ \_ cont -> cont s ()

cgExecST :: IO a -> CrucGen arch ids s a
cgExecST m = CrucGen $ \s cont -> m >>= cont s

-- | A NatRepr corresponding to the architecture width.
archAddrWidth :: CrucGen arch ids s (ArchAddrWidthRepr arch)
archAddrWidth = crucGenAddrWidth . translateFns <$> get

-- | Get current position
getPos :: CrucGen arch ids s C.Position
getPos = gets codePos

addStmt :: CR.Stmt (MacawExt arch) s -> CrucGen arch ids s ()
addStmt stmt = seq stmt $ do
  p <- getPos
  s <- get
  let pstmt = C.Posd p stmt
  let prev = prevStmts s
  seq pstmt $ seq prev $ do
  put $! s { prevStmts = pstmt : prev }

addTermStmt :: CR.TermStmt s (MacawFunctionResult arch)
            -> CrucGen arch ids s a
addTermStmt tstmt = do
  CrucGen $ \s _ -> pure (s, tstmt)
{-
  let termPos = macawPositionFn s (codeOff s)
  let lbl = blockLabel s
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = CR.mkBlock (CR.LabelID lbl) Set.empty stmts term
  pure $ (crucPState s, blk)
-}

-- | Add an extra block, to be returned eventually by 'runCrucGen'.
-- Note that this block has to have been created manually using
-- 'CR.mkBlock' rather than using 'addStmt' and friends.  (TODO:
-- Support a friendlier API such as that of Crucible's Generator
-- monad.)
addExtraBlock :: CR.Block (MacawExt arch) s (MacawFunctionResult arch)
              -> CrucGen arch ids s ()
addExtraBlock blk =
  modify' $ \s@(CrucGenState { extraBlocks = blks }) ->
              s { extraBlocks = blk : blks }

freshValueIndex :: CrucGen arch ids s (Nonce s tp)
freshValueIndex = do
  s <- get
  let ps = crucPState s
  let ng = nonceGen ps
  cgExecST $ freshNonce ng

mmNonceGenerator :: MacawMonad arch ids s (NonceGenerator IO s)
mmNonceGenerator = gets nonceGen

mmFreshNonce :: MacawMonad arch ids s (Nonce s tp)
mmFreshNonce = do
  ng <- gets nonceGen
  mmExecST $ freshNonce ng

mkAtom :: C.TypeRepr ctp -> CrucGen arch ids s (CR.Atom s ctp)
mkAtom tp = do
  archFns <- gets translateFns
  crucGenArchConstraints archFns $ do
  p <- getPos
  i <- freshValueIndex
  -- Make atom
  let atom = CR.Atom { CR.atomPosition = p
                     , CR.atomId = i
                     , CR.atomSource = CR.Assigned
                     , CR.typeOfAtom = tp
                     }
  pure $! atom

-- | Evaluate the crucible app and return a reference to the result.
evalAtom :: CR.AtomValue (MacawExt arch) s ctp -> CrucGen arch ids s (CR.Atom s ctp)
evalAtom av = do
  archFns <- gets translateFns
  crucGenArchConstraints archFns $ do
  atom <- mkAtom (CR.typeOfAtomValue av)
  addStmt $ CR.DefineAtom atom av
  pure atom

-- | Evaluate the crucible app and return a reference to the result.
crucibleValue :: C.App (MacawExt arch) (CR.Atom s) ctp -> CrucGen arch ids s (CR.Atom s ctp)
crucibleValue = evalAtom . CR.EvalApp

-- | Evaluate a Macaw expression extension
evalMacawExt :: MacawExprExtension arch (CR.Atom s) tp -> CrucGen arch ids s (CR.Atom s tp)
evalMacawExt = crucibleValue . C.ExtensionApp

-- | Treat a register value as a bit-vector.
toBits ::
  (1 <= w) =>
  NatRepr w ->
  CR.Atom s (MM.LLVMPointerType w) ->
  CrucGen arch ids s (CR.Atom s (C.BVType w))
toBits w x =
  use (toBitsCacheLens . atF (PtrAtom x)) >>= \case
    Just (BVAtom x') ->
      return x'
    Nothing -> do
      x' <- evalMacawExt (PtrToBits w x)
      assign (toBitsCacheLens . atF (PtrAtom x)) (Just (BVAtom x'))
      assign (fromBitsCacheLens . atF (BVAtom x')) (Just (PtrAtom x))
      return x'

-- | Treat a bit-vector as a register value.
fromBits ::
  (1 <= w) =>
  NatRepr w ->
  CR.Atom s (C.BVType w) ->
  CrucGen arch ids s (CR.Atom s (MM.LLVMPointerType w))
fromBits w x =
  use (fromBitsCacheLens . atF (BVAtom x)) >>= \case
    Just (PtrAtom x') ->
      return x'
    Nothing -> do
      x' <- evalMacawExt (BitsToPtr w x)
      assign (fromBitsCacheLens . atF (BVAtom x)) (Just (PtrAtom x'))
      assign (toBitsCacheLens . atF (PtrAtom x')) (Just (BVAtom x))
      return x'

getRegs :: CrucGen arch ids s (CR.Atom s (ArchRegStruct arch))
getRegs = gets crucRegisterReg >>= evalAtom . CR.ReadReg

-- | Return the value associated with the given register
getRegValue :: M.ArchReg arch tp
            -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
getRegValue r = do
  archFns <- gets translateFns
  idxMap  <- gets crucRegIndexMap
  crucGenArchConstraints archFns $ do
  case MapF.lookup r idxMap of
    Nothing -> fail $ "internal: Register is not bound."
    Just idx -> do
      reg <- gets crucRegisterReg
      regStruct <- evalAtom (CR.ReadReg reg)
      let tp = crucArchRegTypes archFns Ctx.! crucibleIndex idx
      crucibleValue (C.GetStruct regStruct (crucibleIndex idx) tp)

v2c :: M.Value arch ids tp
    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
v2c = valueToCrucible

v2c' :: (1 <= w) =>
       NatRepr w ->
       M.Value arch ids (M.BVType w) ->
       CrucGen arch ids s (CR.Atom s (C.BVType w))
v2c' w x = toBits w =<< valueToCrucible x

-- | Evaluate the crucible app and return a reference to the result.
appAtom :: C.App (MacawExt arch) (CR.Atom s) ctp ->
            CrucGen arch ids s (CR.Atom s ctp)
appAtom app = evalAtom (CR.EvalApp app)

appBVAtom ::
  (1 <= w) =>
  NatRepr w ->
  C.App (MacawExt arch) (CR.Atom s) (C.BVType w) ->
  CrucGen arch ids s (CR.Atom s (MM.LLVMPointerType w))
appBVAtom w app = fromBits w =<< appAtom app

addLemma :: (1 <= x, x + 1 <= y) => NatRepr x -> q y -> LeqProof 1 y
addLemma x y =
  leqProof n1 x `leqTrans`
  leqAdd (leqRefl x) n1 `leqTrans`
  leqProof (addNat x n1) y
  where
  n1 :: NatRepr 1
  n1 = knownNat


-- | Create a crucible value for a bitvector literal.
bvLit :: (1 <= w) => NatRepr w -> Integer -> CrucGen arch ids s (CR.Atom s (C.BVType w))
bvLit w i = crucibleValue (C.BVLit w (BV.mkBV w i))

bitOp2 :: (1 <= w)
       => NatRepr w
       -> (CR.Atom s (C.BVType w)
           -> CR.Atom s (C.BVType w)
           -> C.App (MacawExt arch) (CR.Atom s) (C.BVType w))
       -> M.Value arch ids (M.BVType w)
       -> M.Value arch ids (M.BVType w)
       -> CrucGen arch ids s (CR.Atom s (MM.LLVMPointerType w))
bitOp2 w f x y = fromBits w =<< appAtom =<< f <$> v2c' w x <*> v2c' w y


appToCrucible
  :: forall arch ids s tp
  . M.App (M.Value arch ids) tp
  -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
appToCrucible app = do
  archFns <- gets translateFns
  crucGenArchConstraints archFns $ do
  case app of
    M.Eq x y ->
      do xv <- v2c x
         yv <- v2c y
         case M.typeRepr x of
           M.BoolTypeRepr -> appAtom (C.BaseIsEq C.BaseBoolRepr xv yv)
           M.BVTypeRepr n ->
             do rW <- archAddrWidth
                case testEquality n (M.addrWidthNatRepr rW) of
                  Just Refl -> evalMacawStmt (PtrEq rW xv yv)
                  Nothing ->
                    appAtom =<< C.BVEq n <$> toBits n xv <*> toBits n yv
           M.FloatTypeRepr _ -> appAtom $ C.FloatEq xv yv
           M.TupleTypeRepr _ -> fail "XXX: Equality on tuples not yet done."
           M.VecTypeRepr{} -> fail "XXX: Equality on vectors not yet done."


    M.Mux tp c t f -> do
      cond <- v2c c
      tv   <- v2c t
      fv   <- v2c f
      case tp of
        M.BoolTypeRepr -> appAtom (C.BaseIte C.BaseBoolRepr cond tv fv)
        M.BVTypeRepr n ->
             do rW <- archAddrWidth
                case testEquality n (M.addrWidthNatRepr rW) of
                  Just Refl -> evalMacawStmt (PtrMux rW cond tv fv)
                  Nothing -> appBVAtom n =<<
                                C.BVIte cond n <$> toBits n tv <*> toBits n fv
        M.FloatTypeRepr fi ->
             appAtom $ C.FloatIte (floatInfoToCrucible fi) cond tv fv
        M.TupleTypeRepr _ -> fail "XXX: Mux on tuples not yet done."
        M.VecTypeRepr{} -> fail "XXX: Mux on vectors not yet done."

    -- Booleans

    M.AndApp x y  -> appAtom =<< C.And     <$> v2c x <*> v2c y
    M.OrApp  x y  -> appAtom =<< C.Or      <$> v2c x <*> v2c y
    M.NotApp x    -> appAtom =<< C.Not     <$> v2c x
    M.XorApp x y  -> appAtom =<< C.BoolXor <$> v2c x <*> v2c y

    -- Tuples

    M.MkTuple macawTypes macawFields -> do
      let crucTypes = typeListToCrucible macawTypes
      crucFields <- macawListToCrucibleM v2c macawFields
      appAtom (C.MkStruct crucTypes crucFields)
    M.TupleField tps x i -> do
      let tp'  = typeToCrucible $ tps P.!! i
      x' <- v2c x
      let sz = macawListSize tps
      let i' = macawListIndexToCrucible sz i
      appAtom $ C.GetStruct x' i' tp'

    -- Vectors

    M.ExtractElement macawEltType macawVec macawIdx -> do
      let crucEltType = typeToCrucible macawEltType
      crucVec <- v2c macawVec
      crucIdx <- crucibleValue (C.NatLit (fromIntegral macawIdx))
      appAtom (C.VectorGetEntry crucEltType crucVec crucIdx)
    M.InsertElement (M.VecTypeRepr _n macawEltType) macawVec macawIdx macawVal -> do
      let crucEltType = typeToCrucible macawEltType
      crucVec <- v2c macawVec
      crucIdx <- crucibleValue (C.NatLit (fromIntegral macawIdx))
      crucVal <- v2c macawVal
      appAtom (C.VectorSetEntry crucEltType crucVec crucIdx crucVal)

    -- Extension operations
    M.Trunc x w -> do
      let wx = M.typeWidth x
      LeqProof <- return (addLemma w wx)
      appBVAtom w =<< C.BVTrunc w wx <$> v2c' wx x

    M.SExt x w -> do
      let wx = M.typeWidth x
      appBVAtom w =<< C.BVSext w wx <$> v2c' wx x

    M.UExt x w -> do
      let wx = M.typeWidth x
      appBVAtom w =<< C.BVZext w wx <$> v2c' wx x

    M.Bitcast v p -> do
      crucValue <- v2c v
      evalMacawExt (MacawBitcast crucValue p)

    -- Bitvector arithmetic
    M.BVAdd w x y -> do
      xv <- v2c x
      yv <- v2c y
      aw <- archAddrWidth
      case testEquality w (M.addrWidthNatRepr aw) of
        Just Refl -> evalMacawStmt (PtrAdd aw xv yv)
        Nothing -> appBVAtom w =<< C.BVAdd w <$> toBits w xv <*> toBits w yv

    -- Here we assume that this does not make sense for pointers.
    M.BVAdc w x y c -> do
      z <- appAtom =<< C.BVAdd w <$> v2c' w x <*> v2c' w y
      d <- appAtom =<< C.BaseIte (C.BaseBVRepr w) <$> v2c c
                                             <*> appAtom (C.BVLit w (BV.one w))
                                             <*> appAtom (C.BVLit w (BV.zero w))
      appBVAtom w (C.BVAdd w z d)

    M.BVSub w x y -> do
      xv <- v2c x
      yv <- v2c y
      aw <- archAddrWidth
      case testEquality w (M.addrWidthNatRepr aw) of
        Just Refl -> evalMacawStmt (PtrSub aw xv yv)
        Nothing -> appBVAtom w =<< C.BVSub w <$> toBits w xv <*> toBits w yv

    M.BVSbb w x y c -> do
      z <- appAtom =<< C.BVSub w <$> v2c' w x <*> v2c' w y
      d <- appAtom =<< C.BaseIte (C.BaseBVRepr w) <$> v2c c
                                             <*> appAtom (C.BVLit w (BV.one w))
                                             <*> appAtom (C.BVLit w (BV.zero w))
      appBVAtom w (C.BVSub w z d)


    M.BVMul w x y -> bitOp2 w (C.BVMul w) x y

    M.BVUnsignedLe x y -> do
      let w = M.typeWidth x
      ptrW <- archAddrWidth
      xv <- v2c x
      yv <- v2c y
      case testEquality w (M.addrWidthNatRepr ptrW) of
        Just Refl -> evalMacawStmt (PtrLeq ptrW xv yv)
        Nothing -> appAtom =<< C.BVUle w <$> toBits w xv <*> toBits w yv

    M.BVUnsignedLt x y -> do
      let w = M.typeWidth x
      ptrW <- archAddrWidth
      xv <- v2c x
      yv <- v2c y
      case testEquality w (M.addrWidthNatRepr ptrW) of
        Just Refl -> evalMacawStmt (PtrLt ptrW xv yv)
        Nothing   -> appAtom =<< C.BVUlt w <$> toBits w xv <*> toBits w yv

    M.BVSignedLe x y ->
      do let w = M.typeWidth x
         appAtom =<< C.BVSle w <$> v2c' w x <*> v2c' w y

    M.BVSignedLt x y ->
      do let w = M.typeWidth x
         appAtom =<< C.BVSlt w <$> v2c' w x <*> v2c' w y

    -- Bitwise operations
    M.BVTestBit x i -> do
      let w = M.typeWidth x
      one <- bvLit w 1
      -- Create mask for ith index
      i_mask <- appAtom =<< C.BVShl w one <$> (toBits w =<< v2c i)
      -- Mask off index
      x_mask <- appAtom =<< C.BVAnd w <$> (toBits w =<< v2c x) <*> pure i_mask
      -- Check to see if result is i_mask
      appAtom (C.BVEq w x_mask i_mask)

    M.BVComplement w x -> appBVAtom w =<< C.BVNot w <$> v2c' w x

    M.BVAnd w x y -> do
      xv <- v2c x
      yv <- v2c y
      aw <- archAddrWidth
      case testEquality w (M.addrWidthNatRepr aw) of
        Just Refl -> evalMacawStmt (PtrAnd aw xv yv)
        Nothing -> appBVAtom w =<< C.BVAnd w <$> toBits w xv <*> toBits w yv

    M.BVXor w x y -> do
      xv <- v2c x
      yv <- v2c y
      aw <- archAddrWidth
      case testEquality w (M.addrWidthNatRepr aw) of
        Just Refl -> evalMacawStmt (PtrXor aw xv yv)
        Nothing -> appBVAtom w =<< C.BVXor w <$> toBits w xv <*> toBits w yv

    M.BVOr  w x y -> bitOp2 w (C.BVOr   w) x y
    M.BVShl w x y -> bitOp2 w (C.BVShl  w) x y
    M.BVShr w x y -> bitOp2 w (C.BVLshr w) x y
    M.BVSar w x y -> bitOp2 w (C.BVAshr w) x y

    M.UadcOverflows x y c -> do
      let w = M.typeWidth x
      r <- MacawOverflows Uadc w <$> v2c' w x <*> v2c' w y <*> v2c c
      evalMacawExt r
    M.SadcOverflows x y c -> do
      let w = M.typeWidth x
      r <- MacawOverflows Sadc w <$> v2c' w x <*> v2c' w y <*> v2c c
      evalMacawExt r
    M.UsbbOverflows x y b -> do
      let w = M.typeWidth x
      r <- MacawOverflows Usbb w <$> v2c' w x <*> v2c' w y <*> v2c b
      evalMacawExt r
    M.SsbbOverflows x y b -> do
      let w = M.typeWidth x
      r <- MacawOverflows Ssbb w <$> v2c' w x <*> v2c' w y <*> v2c b
      evalMacawExt r
    M.PopCount (w :: NatRepr n) x -> case testNatCases (knownNat @1) w of
      NatCaseLT LeqProof -> do
        x' <- v2c' w x
        let bvBit
              :: (1 <= i, i <= n)
              => NatRepr i
              -> CrucGen arch ids s (CR.Atom s (C.BVType n))
            bvBit i | Refl <- minusPlusCancel i (knownNat @1) = do
              b <- appAtom $
                C.BVSelect (subNat i (knownNat @1)) (knownNat @1) w x'
              appAtom $ C.BVZext w (knownNat @1) b
        fromBits w =<<
          foldl
            (\a b -> appAtom =<< C.BVAdd w <$> a <*> b)
            (bvLit w 0)
            (natForEach (knownNat @1) w bvBit)
      NatCaseEQ -> v2c x
      NatCaseGT LeqProof
        | Refl <- plusComm (knownNat @1) w
        , Refl <- plusMinusCancel (knownNat @1) w ->
          -- LeqProof 1 0, but the pattern match checking is not clever enough
          case leqSub2 (LeqProof @(1 + n) @1) (LeqProof @1 @n) of
#if !MIN_VERSION_base(4,12,0)
            -- GHC 8.2.2 will error if we give an explicit pattern match, but also
            -- complain of an incomplete pattern match if we do not, so we have
            -- this case here.
            _ -> error "CruccGen case with 1 <= 0"
#endif
    M.ReverseBytes _w _x -> do
      error "Reverse bytes not yet defined."
    M.Bsf w x -> do
      -- scanBits w C.BVShl returns a bit index where the MSB is 0
      -- Here we subtract that index from (w - 1) to obtain an index from the LSB
      cbe <- scanBits w C.BVShl x
      cwsub1 <- bvLit w (intValue w - 1)
      fromBits w =<< appAtom (C.BVSub w cwsub1 cbe)
    M.Bsr w x -> fromBits w =<< scanBits w C.BVLshr x

-- | Compute either:
--   1) the index (MSB is 0) of the least significant set bit
--      (if C.BVShl is passed as the first argument), or
--   2) the index (LSB is 0) of the most significant set bit
--      (if C.BVLshr is passed).
scanBits :: (1 <= w) =>
  NatRepr w ->
  (NatRepr w -> CR.Atom s (C.BVType w) -> CR.Atom s (C.BVType w) -> C.App (MacawExt arch) (CR.Atom s) (C.BVType w)) ->
  M.Value arch ids (M.BVType w) ->
  CrucGen arch ids s (CR.Atom s (C.BVType w))
scanBits w f vx = do
  cx <- v2c vx >>= toBits w
  -- The index of the most (least) significant set bit is equal to the number of
  -- right (left) shifts needed to "zero" x.
  -- We compute this by by trying every possible shift, checking if the result
  -- of each shift is nonzero (yielding 1 if so, 0 otherwise), and summing.
  isZeros <- forM [1..intValue w-1] $ \i -> do
    shiftAmt <- bvLit w i
    shiftedx <- appAtom (f w cx shiftAmt)
    xIsNonzero <- appAtom (C.BVNonzero w shiftedx)
    appAtom (C.BoolToBV w xIsNonzero)
  czero <- bvLit w 0
  foldM ((appAtom .) . C.BVAdd w) czero isZeros

-- | Convert a Macaw 'M.Value' into a Crucible value ('CR.Atom')
--
-- This is in the 'CrucGen' monad so that it can preserve sharing in terms.
valueToCrucible :: M.Value arch ids tp
                -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
valueToCrucible v = do
 archFns <- gets translateFns
 crucGenArchConstraints archFns $ do
 case v of
    M.BVValue w c -> fromBits w =<< bvLit w c
    M.BoolValue b -> crucibleValue (C.BoolLit b)

    M.RelocatableValue w addr
      | M.addrBase addr == 0 && M.addrOffset addr == 0 ->
          evalMacawExt (MacawNullPtr w)
      | otherwise -> evalMacawStmt (MacawGlobalPtr w addr)
    M.SymbolValue{} -> do
      error "macaw-symbolic does not yet support symbol values."

    M.Initial r ->
      getRegValue r

    M.AssignedValue asgn -> do
      let idx = M.assignId asgn
      amap <- use $ crucPStateLens . assignValueMapLens
      case MapF.lookup idx amap of
        Just (MacawCrucibleValue r) -> pure r
        Nothing ->  fail "internal: Assignment id is not bound."

-- | Create a fresh symbolic value of the given type.
freshSymbolic :: M.TypeRepr tp
              -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
freshSymbolic repr = evalMacawStmt (MacawFreshSymbolic repr)

evalMacawStmt :: MacawStmtExtension arch (CR.Atom s) tp ->
                  CrucGen arch ids s (CR.Atom s tp)
evalMacawStmt = evalAtom . CR.EvalExt

-- | Embed an architecture-specific Macaw statement into a Crucible program
--
-- All architecture-specific statements return values (which can be unit).
evalArchStmt :: MacawArchStmtExtension arch (CR.Atom s) tp -> CrucGen arch ids s (CR.Atom s tp)
evalArchStmt = evalMacawStmt . MacawArchStmtExtension

assignRhsToCrucible :: M.AssignRhs arch (M.Value arch ids) tp
                    -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp))
assignRhsToCrucible rhs =
 gets translateFns >>= \archFns ->
 crucGenArchConstraints archFns $
  case rhs of
    M.EvalApp app -> appToCrucible app
    M.SetUndefined mrepr -> freshSymbolic mrepr
    M.ReadMem addr repr -> do
      caddr <- valueToCrucible addr
      w     <- archAddrWidth
      evalMacawStmt (MacawReadMem w repr caddr)
    M.CondReadMem repr cond addr def -> do
      ccond <- valueToCrucible cond
      caddr <- valueToCrucible addr
      cdef  <- valueToCrucible def
      w     <- archAddrWidth
      evalMacawStmt (MacawCondReadMem w repr ccond caddr cdef)
    M.EvalArchFn f _ -> do
      fns <- translateFns <$> get
      crucGenArchFn fns f

addMacawStmt :: forall arch ids s . M.ArchSegmentOff arch -> M.Stmt arch ids -> CrucGen arch ids s ()
addMacawStmt baddr stmt =
  gets translateFns >>= \archFns ->
  crucGenArchConstraints archFns $
  case stmt of
    M.AssignStmt asgn -> do
      let idx = M.assignId asgn
      a <- assignRhsToCrucible (M.assignRhs asgn)
      crucPStateLens . assignValueMapLens %= MapF.insert idx (MacawCrucibleValue a)
    M.WriteMem addr repr val -> do
      caddr <- valueToCrucible addr
      cval  <- valueToCrucible val
      w     <- archAddrWidth
      void $ evalMacawStmt (MacawWriteMem w repr caddr cval)
    M.CondWriteMem cond addr repr val -> do
      ccond <- valueToCrucible cond
      caddr <- valueToCrucible addr
      cval  <- valueToCrucible val
      w     <- archAddrWidth
      void $ evalMacawStmt (MacawCondWriteMem w repr ccond caddr cval)
    M.InstructionStart off t -> do
      -- Update the position
      modify' $ \s -> s { codeOff = off
                        , codePos = macawPositionFn s off
                        }
      let crucStmt :: MacawStmtExtension arch (CR.Atom s) C.UnitType
          crucStmt = MacawInstructionStart baddr off t
      void $ evalMacawStmt crucStmt
    M.Comment _txt -> do
      pure ()
    M.ExecArchStmt astmt -> do
      fns <- translateFns <$> get
      crucGenArchStmt fns astmt
    M.ArchState addr macawVals -> do
      m <- traverseF (fmap MacawCrucibleValue . valueToCrucible) macawVals
      let crucStmt :: MacawStmtExtension arch (CR.Atom s) C.UnitType
          crucStmt = MacawArchStateUpdate addr m
      void $ evalMacawStmt crucStmt

-- | Create a crucible struct for registers from a register state.
createRegStruct :: forall arch ids s
                .  M.RegState (M.ArchReg arch) (M.Value arch ids)
                -> CrucGen arch ids s (CR.Atom s (ArchRegStruct arch))
createRegStruct regs = do
  archFns <- gets translateFns

  -- IMPORTANT: The registers are never changed in the middle of the
  -- block, ONLY at the ends.  So 'startingVals' will have the value
  -- of each register as it was at the beginning of the block.
  startingVals <- do
    regReg <- gets crucRegisterReg
    evalAtom (CR.ReadReg regReg)

  let addUpdate vals (Pair idx val) = do
        let tps = crucArchRegTypes archFns
        crucibleValue $ C.SetStruct tps vals idx val

  updates <- createRegUpdates regs
  foldM addUpdate startingVals updates

-- | Note that the list of updates is only meant to be used in 'createRegStruct'
-- to populate the register struct being created in that function.  This
-- function does not actually emit any Crucible statements itself.
createRegUpdates :: forall arch ids s
                 .  M.RegState (M.ArchReg arch) (M.Value arch ids)
                 -> CrucGen arch ids s
                      [Pair (Ctx.Index (MacawCrucibleRegTypes arch)) (CR.Atom s)]
createRegUpdates regs = do
  archFns <- gets translateFns
  idxMap <- gets crucRegIndexMap
  crucGenArchConstraints archFns $ do
    fmap catMaybes $ forM (M.regStateMap regs & MapF.toList) $ \(Pair reg val) ->
      case val of
        M.Initial r | Just _ <- testEquality r reg -> return Nothing
        _ -> case MapF.lookup reg idxMap of
          Nothing -> fail "internal: Register is not bound."
          Just idx -> Just . Pair (crucibleIndex idx) <$> valueToCrucible val

addMacawTermStmt :: M.TermStmt arch ids
                 -> CrucGen arch ids s ()
addMacawTermStmt tstmt =
  case tstmt of
    M.FetchAndExecute regs -> do
      s <- createRegStruct regs
      addTermStmt (CR.Return s)
    M.ArchTermStmt ts regs -> do
      fns <- translateFns <$> get
      crucGenArchTermStmt fns ts regs
    M.TranslateError _regs msg -> do
      cmsg <- crucibleValue (C.StringLit (C.UnicodeLiteral msg))
      addTermStmt (CR.ErrorStmt cmsg)

-----------------

-- | Monad for adding new blocks to a state.
newtype MacawMonad arch ids s a
  = MacawMonad ( ExceptT String (StateT (CrucPersistentState ids s) IO) a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError String
           , MonadState (CrucPersistentState ids s)
           )

runMacawMonad :: CrucPersistentState ids s
              -> MacawMonad arch ids s a
              -> IO (Either String a, CrucPersistentState ids s)
runMacawMonad s (MacawMonad m) = runStateT (runExceptT m) s

mmExecST :: IO a -> MacawMonad arch ids s a
mmExecST = MacawMonad . lift . lift

runCrucGen :: forall arch ids s
           .  MacawSymbolicArchFunctions arch
           -> (M.ArchAddrWord arch -> C.Position)
              -- ^ Function for generating position from offset from start of this block.
           -> CR.Label s
              -- ^ Label for this block
           -> CR.Reg s (ArchRegStruct arch)
              -- ^ Crucible register for struct containing all Macaw registers.
           -> CrucGen arch ids s ()
           -> MacawMonad arch ids s
                ( CR.Block (MacawExt arch ) s (MacawFunctionResult arch)
                    -- Block created
                , [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
                    -- Extra blocks created along the way
                )
runCrucGen archFns posFn lbl regReg action = crucGenArchConstraints archFns $ do
  ps <- get
  let regAssign = crucGenRegAssignment archFns
  let crucRegTypes = crucArchRegTypes archFns
  let s0 = CrucGenState { translateFns = archFns
                        , crucRegIndexMap = mkRegIndexMap regAssign (Ctx.size crucRegTypes)
                        , crucPState = ps
                        , crucRegisterReg = regReg
                        , macawPositionFn = posFn
                        , blockLabel = lbl
                        , codeOff    = 0
                        , codePos    = posFn 0
                        , prevStmts  = []
                        , toBitsCache = MapF.empty
                        , fromBitsCache = MapF.empty
                        , extraBlocks = []
                        }
  let cont _s () = fail "Unterminated crucible block"
  (s, tstmt)  <- mmExecST $ unCrucGen action s0 cont
  put (crucPState s)
  let termPos = posFn (codeOff s)
  let stmts = Seq.fromList (reverse (prevStmts s))
  let term = C.Posd termPos tstmt
  let blk = CR.mkBlock (CR.LabelID lbl) Set.empty stmts term
  let !blks = reverse (extraBlocks s)
  pure (blk, blks)

addMacawBlock :: M.MemWidth (M.ArchAddrWidth arch)
              => MacawSymbolicArchFunctions arch
              -> M.ArchSegmentOff arch
                 -- ^ Address of start of block
              -> CR.Label s
                 -- ^ Crucible label for this bloclk.
              -> (M.ArchAddrWord arch -> C.Position)
                 -- ^ Function for generating position from offset from start of this block.
              -> M.Block arch ids
              -> MacawMonad arch ids s
                   ( CR.Block (MacawExt arch) s (MacawFunctionResult arch)
                   , [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
                   )
addMacawBlock archFns addr lbl posFn b = do
  let archRegStructRepr = C.StructRepr (crucArchRegTypes archFns)
  ng <- gets nonceGen
  regRegId <- mmExecST $ freshNonce ng
  let regReg = CR.Reg { CR.regPosition = posFn 0
                      , CR.regId = regRegId
                      , CR.typeOfReg = archRegStructRepr
                      }
  regStructId <- mmExecST $ freshNonce ng
  let regStruct = CR.Atom { CR.atomPosition = C.InternalPos
                          , CR.atomId = regStructId
                          , CR.atomSource = CR.FnInput
                          , CR.typeOfAtom = archRegStructRepr
                          }
  runCrucGen archFns posFn lbl regReg $ do
    addStmt $ CR.SetReg regReg regStruct
    mapM_ (addMacawStmt addr)  (M.blockStmts b)
    addMacawTermStmt (M.blockTerm b)

parsedBlockLabel :: (Ord addr, Show addr)
                 => Map addr (CR.Label s)
                    -- ^ Map from block addresses to starting label
                 -> addr
                 -> CR.Label s
parsedBlockLabel blockLabelMap addr =
  fromMaybe (error $ "Could not find entry point: " ++ show addr) $
  Map.lookup addr blockLabelMap

-- | DO NOT CALL THIS FROM USER CODE.  We count on the registers not
-- changing until the end of the block.
setMachineRegs :: CR.Atom s (ArchRegStruct arch) -> CrucGen arch ids s ()
setMachineRegs newRegs = do
  regReg <- gets crucRegisterReg
  addStmt $ CR.SetReg regReg newRegs

-- | Map from block information to Crucible label (used to generate term statements)
type BlockLabelMap arch s = Map (M.ArchSegmentOff arch) (CR.Label s)

addMacawParsedTermStmt :: BlockLabelMap arch s
                          -- ^ Block label map for this function
                       -> [(M.ArchSegmentOff arch, [M.ArchSegmentOff arch])]
                       -- ^ ClassifyFailure resolutions discovered from external
                       -- means (attached to the DiscoveryFunInfo if available)
                       --
                       -- The keys are the addresses of the blocks that have
                       -- resolved ClassifyFailures
                       -> M.ArchSegmentOff arch
                          -- ^ Address of this block
                       -> M.ParsedTermStmt arch ids
                       -> CrucGen arch ids s ()
addMacawParsedTermStmt blockLabelMap externalResolutions thisAddr tstmt = do
 archFns <- translateFns <$> get
 crucGenArchConstraints archFns $ do
  case tstmt of
    M.ParsedCall regs mret -> do
      curRegs <- createRegStruct regs
      let tps = typeCtxToCrucible $ fmapFC M.typeRepr $ crucGenRegAssignment archFns
      fh <- evalMacawStmt (MacawLookupFunctionHandle (crucArchRegTypes archFns) curRegs)
      newRegs <- evalAtom $ CR.Call fh (Ctx.singleton curRegs) (C.StructRepr tps)
      case mret of
        Just nextAddr -> do
          setMachineRegs newRegs
          addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap nextAddr)
        Nothing ->
          addTermStmt $ CR.Return newRegs
    M.ParsedJump regs nextAddr -> do
      setMachineRegs =<< createRegStruct regs
      addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap nextAddr)
    M.ParsedBranch regs c trueAddr falseAddr -> do
      setMachineRegs =<< createRegStruct regs
      crucCond <- valueToCrucible c
      let tlbl = parsedBlockLabel blockLabelMap trueAddr
      let flbl = parsedBlockLabel blockLabelMap falseAddr
      addTermStmt $! CR.Br crucCond tlbl flbl
    M.ParsedLookupTable _layout regs idx possibleAddrs -> do
      setMachineRegs =<< createRegStruct regs
      addSwitch blockLabelMap idx possibleAddrs
    M.ParsedReturn regs -> do
      regValues <- createRegStruct regs
      addTermStmt $ CR.Return regValues
    M.ParsedArchTermStmt aterm regs mnextAddr -> do
      crucGenArchTermStmt archFns aterm regs
      case mnextAddr of
        Just nextAddr -> addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap nextAddr)
        -- There won't be a next instruction if, for instance, this is
        -- an X86 HLT instruction.  TODO: We may want to do something
        -- else for an exit syscall, since that's a normal outcome.
        Nothing -> do
          msgVal <- crucibleValue (C.StringLit (C.UnicodeLiteral "Halting"))
          addTermStmt $ CR.ErrorStmt msgVal
    M.PLTStub{} ->
      error "Do not support translating PLT stubs"
    M.ParsedTranslateError msg -> do
      msgVal <- crucibleValue (C.StringLit (C.UnicodeLiteral msg))
      addTermStmt $ CR.ErrorStmt msgVal
    M.ClassifyFailure regs _failureReasons
      | Just targets <- lookup thisAddr externalResolutions -> do
          setMachineRegs =<< createRegStruct regs
          addIPSwitch blockLabelMap targets (regs ^. M.boundValue M.ip_reg)
      | otherwise -> do
          msgVal <- crucibleValue $ C.StringLit $ C.UnicodeLiteral $ Text.pack ("Could not identify block at " ++ show thisAddr ++ " with external resolutions: " ++ show externalResolutions)
          addTermStmt $ CR.ErrorStmt msgVal

-- | This is like 'addSwitch', but for unstructured indirect control flow
--
-- The 'addSwitch' function handles jump tables that are indexed by a bitvector
-- (i.e., the 'M.ArchAddrValue' in 'addSwitch').  This variant is different hand
-- handles indirect control flow that does not go through a jump table (or goes
-- through a jump table that the static pattern matching in macaw could not
-- handle).
--
-- In this case, the possible target addresses are in the @targets@ parameter.
-- We construct a tree of if-then-else branches that check the computed IP
-- address of the jump and jump to the corresponding block if there is a match.
-- If there is no match, it turns into a simulator error statement.  The error
-- could be hit if the macaw analysis was incorrect.
addIPSwitch :: forall arch s ids
             . BlockLabelMap arch s
            -> [M.ArchSegmentOff arch]
            -- ^ The possible branch targets
            -> M.Value arch ids (M.BVType (M.ArchAddrWidth arch))
            -- ^ The IP we are branching to
            -> CrucGen arch ids s ()
addIPSwitch blockLabelMap targets macaw_ip = do
  archFns <- translateFns <$> get
  crucGenArchConstraints archFns $ do
    p <- getPos
    -- Convert the current IP value (taken from the reg state at the terminator)
    -- into a Crucible value
    ipVal <- v2c macaw_ip
    let chain :: ( [CR.Stmt (MacawExt arch) s]
                 , CR.TermStmt s (MacawFunctionResult arch)
                 )
              -> M.ArchSegmentOff arch
              -> CrucGen arch ids s
                 ( [CR.Stmt (MacawExt arch) s]
                 , CR.TermStmt s (MacawFunctionResult arch)
                 )
        chain (elseStmts, elseTerm) thenAddr = do
          elseLbl <- CR.Label <$> freshValueIndex
          let elseBlock = CR.mkBlock (CR.LabelID elseLbl) Set.empty
                             (Seq.fromList (map (C.Posd p) elseStmts))
                             (C.Posd p elseTerm)
          addExtraBlock elseBlock

          let widthRepr = M.addrWidthRepr (Proxy @(M.ArchAddrWidth arch))
          let width = M.addrWidthNatRepr widthRepr
          let bvRepr = C.BVRepr width
          let ptrRepr = MM.LLVMPointerRepr width
          eqAtom <- mkAtom C.BoolRepr
          ptrBitsAtom <- mkAtom bvRepr
          ptrAtom <- mkAtom ptrRepr

          let targetLbl = parsedBlockLabel blockLabelMap thenAddr
          let Just bvAddr = M.segoffAsAbsoluteAddr thenAddr
          -- Make a Crucible instruction sequence that compares the current IP
          -- against a possible target taken from the input list.
          return ( [ CR.DefineAtom ptrBitsAtom $ CR.EvalApp $ C.BVLit width (BV.mkBV width (toInteger bvAddr))
                   , CR.DefineAtom ptrAtom $ CR.EvalApp $ C.ExtensionApp $ BitsToPtr width ptrBitsAtom
                   , CR.DefineAtom eqAtom $ CR.EvalExt $ PtrEq widthRepr ipVal ptrAtom
                   ]
                 , CR.Br eqAtom targetLbl elseLbl
                 )

    errAtom <- mkAtom (C.StringRepr C.UnicodeRepr)
    let finalStmts = [ CR.DefineAtom errAtom $ CR.EvalApp $ C.StringLit $ C.UnicodeLiteral "IP target not recovered for jump table"
                     ]
    let finalTermStmt = CR.ErrorStmt errAtom
    (stmts, termStmt) <- F.foldlM chain (finalStmts, finalTermStmt) targets
    mapM_ addStmt stmts
    addTermStmt termStmt

addSwitch :: forall arch s ids
           . BlockLabelMap arch s
          -> M.ArchAddrValue arch ids
          -> Vec.Vector (M.ArchSegmentOff arch)
          -> CrucGen arch ids s ()
addSwitch blockLabelMap idx possibleAddrs = do
  archFns <- translateFns <$> get
  crucGenArchConstraints archFns $ do

  p <- getPos
  idxVal <- v2c idx

  let -- Add a link to the if-else chain, going from the bottom up.
      -- That is, take the current "else" code and an index-address
      -- pair from the jump table, and construct a branch that goes
      -- either to that address or to that "else".
      --
      -- Note that it's tempting to use a single 'CR.VariantElim' here
      -- rather than build a whole bunch of blocks in an if-else
      -- chain.  Sadly, two things go wrong.  First, you need a way to
      -- construct a variant with a statically-unknown tag.  This
      -- isn't currently possible but wouldn't (I think?) be hard to
      -- add.  More seriously, 'CR.VariantElim' requires the target
      -- labels to be 'CR.LambdaLabel's, not 'CR.Label's.  So you'd
      -- need to add a bunch of shim blocks anyway (or refactor the
      -- CFG datatypes to eliminate the distinction between a label
      -- and a lambda label taking 'C.UnitType').  This might be worth
      -- reconsidering if these (potentially very long) chains become
      -- a problem.
      chain :: ( [CR.Stmt (MacawExt arch) s]
               , CR.TermStmt s (MacawFunctionResult arch) )
            -> ( Int
               , M.ArchSegmentOff arch )
            -> CrucGen arch ids s
                 ( [CR.Stmt (MacawExt arch) s]
                 , CR.TermStmt s (MacawFunctionResult arch) )
      chain (elsStmts, elsTerm) (thnIdx, thnAddr) = do
        elsLbl <- CR.Label <$> freshValueIndex
        let elsBlk =
              CR.mkBlock (CR.LabelID elsLbl) Set.empty
                (Seq.fromList (map (C.Posd p) elsStmts))
                (C.Posd p elsTerm)
        addExtraBlock elsBlk

        -- TODO: This is awkward.  We would like to use @evalAtom@ and
        -- @crucibleValue@ and such, but we can't because those add
        -- statements to *this* block.  Would be nice if we could do
        -- what Crucible's own Generator monad allows and define a
        -- block in a nested fashion.

        -- FIXME: None of the following four things should be
        -- necessary to spell out, but the right KnownRepr instances
        -- aren't available to make knownRepr work on its own.
        let widthRepr = M.addrWidthRepr (Proxy @(M.ArchAddrWidth arch))
            width = M.addrWidthNatRepr widthRepr
            bvRepr = C.BVRepr width
            ptrRepr = MM.LLVMPointerRepr width
        thnIdxBitsAtom <- mkAtom bvRepr
        thnIdxAtom <- mkAtom ptrRepr
        eqAtom <- mkAtom C.BoolRepr

        let thnLbl = parsedBlockLabel blockLabelMap thnAddr

        return ( [ CR.DefineAtom thnIdxBitsAtom $
                     CR.EvalApp $ C.BVLit width (BV.mkBV width (toInteger thnIdx))
                 , CR.DefineAtom thnIdxAtom $
                     CR.EvalApp $ C.ExtensionApp $
                       BitsToPtr width thnIdxBitsAtom
                 , CR.DefineAtom eqAtom $
                     CR.EvalExt $ PtrEq widthRepr idxVal thnIdxAtom
                 ]
               , CR.Br eqAtom thnLbl elsLbl
               )

  errAtom <- mkAtom (C.StringRepr C.UnicodeRepr)
  let finalStmts =
        [ CR.DefineAtom errAtom $ CR.EvalApp $ C.StringLit $ C.UnicodeLiteral
            "Index not in lookup table"
        ]
  let finalTermStmt = CR.ErrorStmt errAtom

  (stmts, termStmt) <-
    Vec.foldM chain (finalStmts, finalTermStmt)
      -- Build in bottom-up order but keep the original indices
      (Vec.reverse (Vec.indexed possibleAddrs))

  mapM_ addStmt stmts
  addTermStmt termStmt

addParsedBlock :: forall arch ids s
               .  MacawSymbolicArchFunctions arch
               -> BlockLabelMap arch s
               -- ^ Map from block index to Crucible label
               -> [(M.ArchSegmentOff arch, [M.ArchSegmentOff arch])]
               -- ^ External resolutions to ClassifyFailures
               -> (M.ArchSegmentOff arch -> C.Position)
               -- ^ Function for generating position from offset from start of this block.
               -> CR.Reg s (ArchRegStruct arch)
                    -- ^ Register that stores Macaw registers
               -> M.ParsedBlock arch ids
               -> MacawMonad arch ids s [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]
addParsedBlock archFns blockLabelMap externalResolutions posFn regReg macawBlock = do
  crucGenArchConstraints archFns $ do
  let base = M.pblockAddr macawBlock
  let thisPosFn :: M.ArchAddrWord arch -> C.Position
      thisPosFn off = posFn r
        where Just r = M.incSegmentOff base (toInteger off)
  let startAddr = M.pblockAddr macawBlock
  lbl <-
    case Map.lookup startAddr blockLabelMap of
      Just lbl ->
        pure lbl
      Nothing ->
        throwError $ "Internal: Could not find block with address " ++ show startAddr
  (b,bs) <-
    runCrucGen archFns thisPosFn lbl regReg $ do
      mapM_ (addMacawStmt startAddr) (M.pblockStmts  macawBlock)
      addMacawParsedTermStmt blockLabelMap externalResolutions startAddr (M.pblockTermStmt macawBlock)
  pure (reverse (b : bs))

traverseArchStateUpdateMap :: (Applicative m)
                           => (forall tp . e tp -> m (f tp))
                           -> MapF.MapF k (MacawCrucibleValue e)
                           -> m (MapF.MapF k (MacawCrucibleValue f))
traverseArchStateUpdateMap f m = MapF.traverseWithKey (\_ v -> traverseFC f v) m

--------------------------------------------------------------------------------
-- Auto-generated instances

$(return [])

instance TestEqualityFC (MacawExprExtension arch) where
  testEqualityFC f =
    $(U.structuralTypeEquality [t|MacawExprExtension|]
      [ (U.DataArg 1                      `U.TypeApp` U.AnyType, [|f|])
      , (U.ConType [t|NatRepr |]          `U.TypeApp` U.AnyType, [|testEquality|])
      , (U.ConType [t|ArchAddrWidthRepr|] `U.TypeApp` U.AnyType, [|testEquality|])
      , (U.ConType [t|M.WidthEqProof|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType,
          [|M.widthEqProofEq|])

      ])

instance OrdFC (MacawExprExtension arch) where
  compareFC f =
    $(U.structuralTypeOrd [t|MacawExprExtension|]
      [ (U.DataArg 1                      `U.TypeApp` U.AnyType,        [|f|])
      , (U.ConType [t|NatRepr|]           `U.TypeApp` U.AnyType,        [|compareF|])
      , (U.ConType [t|ArchAddrWidthRepr|] `U.TypeApp` U.AnyType,        [|compareF|])
      , (U.ConType [t|M.WidthEqProof|] `U.TypeApp` U.AnyType `U.TypeApp` U.AnyType,
          [|M.widthEqProofCompare|])
      ])

instance FunctorFC (MacawExprExtension arch) where
  fmapFC = fmapFCDefault

instance FoldableFC (MacawExprExtension arch) where
  foldMapFC = foldMapFCDefault

instance TraversableFC (MacawExprExtension arch) where
  traverseFC =
    $(U.structuralTraversal [t|MacawExprExtension|] [])

instance TraversableFC (MacawArchStmtExtension arch)
      => TraversableFC (MacawStmtExtension arch) where
  traverseFC =
    $(U.structuralTraversal [t|MacawStmtExtension|]
      [ (U.ConType [t|MacawArchStmtExtension|] `U.TypeApp` U.DataArg 0
                                               `U.TypeApp` U.DataArg 1
                                               `U.TypeApp` U.DataArg 2
        , [|traverseFC|])
      , (U.ConType [t|MapF.MapF|] `U.TypeApp` U.AnyType
                                  `U.TypeApp` U.AnyType
        , [|traverseArchStateUpdateMap|])
      ]
     )
