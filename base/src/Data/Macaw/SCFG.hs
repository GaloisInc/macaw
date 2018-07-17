{-|
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This exports the "simplifiable CFG" interface.  A CFG designed for
optimization.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.SCFG
  ( SCFG(..)
  , SCFGBlock(..)
  , CallingConvention(..)
  , TermStmt(..)
  , module Data.Macaw.CFG.App
  ) where

import           Data.Macaw.CFG.AssignRhs
import           Data.Macaw.CFG.App
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
  -- | A constant bitvector
  --
  -- The integer should be between 0 and 2^n-1.
  BVValue :: (1 <= n)
          => !(NatRepr n)
          -> !Integer
          -> Value arch ids (BVType n)
  -- | A constant Boolean
  BoolValue :: !Bool -> Value arch ids BoolType
  -- | A memory address
  RelocatableValue :: !(AddrWidthRepr (ArchAddrWidth arch))
                   -> !(ArchMemAddr arch)
                   -> Value arch ids (BVType (ArchAddrWidth arch))
  -- | Reference to a symbol identifier.
  --
  -- This appears when dealing with relocations.
  SymbolValue :: !(AddrWidthRepr (ArchAddrWidth arch))
              -> !SymbolIdentifier
              -> Value arch ids (BVType (ArchAddrWidth arch))
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
