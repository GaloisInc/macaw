{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Macaw AST elements used after block classification
--
-- There are two stages of code discovery:
--
-- 1. Initial discovery with simple block terminators (unclassified block terminators like FetchAndExecute)
--
-- 2. Classified block terminators (e.g., branch, call, return, etc)
--
-- This module defines the AST elements for the latter case.
module Data.Macaw.Discovery.ParsedContents (
    ParsedTermStmt(..)
  , parsedTermSucc
  , ParsedBlock(..)
  , ParsedContents(..)
  , Extension(..)
  , BlockExploreReason(..)
  -- * JumpTableLayout
  , JumpTableLayout(..)
  , jtlBackingAddr
  , jtlBackingSize
  -- * BoundedMemArray
  , BoundedMemArray(..)
  , arByteCount
  , isReadOnlyBoundedMemArray
  -- * Pretty Printing
  , ppTermStmt
  ) where

import qualified Control.Lens as CL
import           Data.Maybe ( maybeToList )
import qualified Data.Parameterized.Map as MapF
import           Data.Text ( Text )
import qualified Data.Vector as V
import           Data.Word ( Word64 )
import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )

import           Data.Macaw.AbsDomain.AbsState ( AbsBlockState )
import           Data.Macaw.CFG
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

------------------------------------------------------------------------
-- BlockExploreReason

-- | This describes why we are exploring a given block within a function.
data BlockExploreReason w
   --   -- | Exploring because the given block writes it to memory.
   --  =- InWrite !(MemSegmentOff w)
     -- | Exploring because the given block jumps here.
   = NextIP !(MemSegmentOff w)
     -- | Identified as an entry point from initial information
   | FunctionEntryPoint
     -- | Added because the address split this block after it had been
     -- disassembled.  Also includes the reason we thought the block
     -- should be there before we split it.
   | SplitAt !(MemSegmentOff w) !(BlockExploreReason w)
     -- The user requested that we analyze this address as a function.
     -- UserRequest

  deriving (Eq, Show)

instance MemWidth w => PP.Pretty (BlockExploreReason w) where
  pretty (NextIP b) = "next address after block " <> PP.pretty b
  pretty FunctionEntryPoint = "function entry point"
  pretty (SplitAt o prior) =
    PP.vcat
      [ "split at offset" PP.<+> PP.pretty o <> ", previously reachable from:"
      , PP.indent 2 (PP.pretty prior)
      ]

-------------------------------------------------------------------------------
-- BoundedMemArray

-- | This describes a region of memory dereferenced in some array read.
--
-- These regions may be be sparse, given an index @i@, the
-- the address given by @arBase@ + @arIx'*'arStride@.
data BoundedMemArray arch tp = BoundedMemArray
  { arBase   :: !(ArchSegmentOff arch)
    -- ^ The base address for array accesses.
  , arStride :: !Word64
    -- ^ Space between elements of the array.
    --
    -- This will typically be the number of bytes denoted by `arEltType`,
    -- but may be larger for sparse arrays.  `matchBoundedMemArray` will fail
    -- if stride is less than the number of bytes read.
  , arEltType   :: !(MemRepr tp)
    -- ^ Resolved type of elements in this array.
  , arSlices       :: !(V.Vector [MemChunk (ArchAddrWidth arch)])
    -- ^ The slices of memory in the array.
    --
    -- The `i`th element in the vector corresponds to the first `size`
    -- bytes at address `base + stride * i`.
    --
    -- The number of elements is the length of the array.
    --
    -- N.B.  With the size could be computed from the previous fields,
    -- but we check we can create it when creating the array read, so
    -- we store it to avoid recomputing it.
  }

deriving instance RegisterInfo (ArchReg arch) => Show (BoundedMemArray arch tp)

-- | Return number of bytes used by this array.
arByteCount :: BoundedMemArray arch tp -> Word64
arByteCount a = arStride a * fromIntegral (V.length (arSlices a))

-- | Return true if the address stored is readable and not writable.
isReadOnlyBoundedMemArray :: BoundedMemArray arch  tp -> Bool
isReadOnlyBoundedMemArray = Perm.isReadonly . segmentFlags . segoffSegment . arBase

------------------------------------------------------------------------
-- Extension

-- | Information about a value that is the signed or unsigned extension of another
-- value.
--
-- This is used for jump tables, and only supports widths that are in memory
data Extension w = Extension { _extIsSigned :: !Bool
                             , _extWidth :: !(AddrWidthRepr w)
                               -- ^ Width of argument. is to.
                             }
  deriving (Show)


------------------------------------------------------------------------
-- JumpTableLayout

-- | This describes the layout of a jump table.
-- Beware: on some architectures, after reading from the jump table, the
-- resulting addresses must be aligned. See the IPAlignment class.
data JumpTableLayout arch
  = AbsoluteJumpTable !(BoundedMemArray arch (BVType (ArchAddrWidth arch)))
  -- ^ @AbsoluteJumpTable r@ describes a jump table where the jump
  -- target is directly stored in the array read @r@.
  | forall w . RelativeJumpTable !(ArchSegmentOff arch)
                                 !(BoundedMemArray arch (BVType w))
                                 !(Extension w)
  -- ^ @RelativeJumpTable base read ext@ describes information about a
  -- jump table where all jump targets are relative to a fixed base
  -- address.
  --
  -- The value is computed as @baseVal + readVal@ where
  --
  -- @baseVal = fromMaybe 0 base@, @readVal@ is the value stored at
  -- the memory read described by @read@ with the sign of @ext@.

deriving instance RegisterInfo (ArchReg arch) => Show (JumpTableLayout arch)

-- | Return base address of table storing contents of jump table.
jtlBackingAddr :: JumpTableLayout arch ->  ArchSegmentOff arch
jtlBackingAddr (AbsoluteJumpTable a) = arBase a
jtlBackingAddr (RelativeJumpTable _ a _) = arBase a

-- | Returns the number of bytes in the layout
jtlBackingSize :: JumpTableLayout arch -> Word64
jtlBackingSize (AbsoluteJumpTable a) = arByteCount a
jtlBackingSize (RelativeJumpTable _ a _) = arByteCount a

------------------------------------------------------------------------
-- ParsedTermStmt

-- | This term statement is used to describe higher level expressions
-- of how block ending with a a FetchAndExecute statement should be
-- interpreted.
data ParsedTermStmt arch ids
  -- | A call with the current register values and location to return
  -- to or 'Nothing' if this is a tail call.
  --
  -- Note that the semantics of this instruction assume that the
  -- program has already stored the return address in the appropriate
  -- location (which depends on the ABI).  For example on X86_64 this
  -- is the top of the stack while on ARM this is the link register.
  = ParsedCall !(RegState (ArchReg arch) (Value arch ids))
               !(Maybe (ArchSegmentOff arch))
    -- | @PLTStub regs addr sym symVer@ denotes a terminal statement that
    -- has been identified as a PLT stub for jumping to the given symbol
    -- (with optional version information).
    --
    -- This is a special case of a tail call.  It has been added
    -- separately because it occurs frequently in dynamically linked
    -- code, and we can use this to recognize PLT stubs.
    --
    -- The first argument maps registers that were changed to their
    -- value.  Other registers have the initial value.  This should
    -- typically be empty on @X86_64@ PLT stubs.
    --
    -- The second argument is the address in the .GOT that the target
    -- function is stored at.  The PLT stub sets the PC to the address
    -- stored here.
    --
    -- The third and fourth arguments are used to resolve where the
    -- function should jump to.
  | PLTStub !(MapF.MapF (ArchReg arch) (Value arch ids))
            !(ArchSegmentOff arch)
            !VersionedSymbol
  -- | A jump to an explicit address within a function.
  | ParsedJump !(RegState (ArchReg arch) (Value arch ids)) !(ArchSegmentOff arch)
  -- | @ParsedBranch regs cond trueAddr falseAddr@ represents a conditional
  -- branch that jumps to @trueAddr@ if @cond@ is true and @falseAddr@ otherwise.
  --
  -- The value assigned to the IP in @regs@ should reflect this if-then-else
  -- structure.
  | ParsedBranch !(RegState (ArchReg arch) (Value arch ids))
                 !(Value arch ids BoolType)
                 !(ArchSegmentOff arch)
                 !(ArchSegmentOff arch)
  -- | A lookup table that branches to one of a vector of addresses.
  --
  -- The registers store the registers, the value contains the index to jump
  -- to, and the possible addresses as a table.  If the index (when interpreted as
  -- an unsigned number) is larger than the number of entries in the vector, then the
  -- result is undefined.
  | ParsedLookupTable !(JumpTableLayout arch)
                      !(RegState (ArchReg arch) (Value arch ids))
                      !(ArchAddrValue arch ids)
                      !(V.Vector (ArchSegmentOff arch))
  -- | A return with the given registers.
  | ParsedReturn !(RegState (ArchReg arch) (Value arch ids))
  -- | An architecture-specific statement with the registers prior to execution, and
  -- the given next control flow address.
  | ParsedArchTermStmt !(ArchTermStmt arch (Value arch ids))
                       !(RegState (ArchReg arch) (Value arch ids))
                       !(Maybe (ArchSegmentOff arch))
  -- | An error occured in translating the block
  | ParsedTranslateError !Text
  -- | The classifier failed to identity the block.
  -- Includes registers with list of reasons for each classifer to fail
  | ClassifyFailure !(RegState (ArchReg arch) (Value arch ids)) [String]

ppTermStmt :: ArchConstraints arch
           => ParsedTermStmt arch ids
           -> PP.Doc ann
ppTermStmt tstmt =
  case tstmt of
    ParsedCall s Nothing ->
      PP.vcat
      [ "tail_call"
      , PP.indent 2 (PP.pretty s) ]
    ParsedCall s (Just next) ->
      PP.vcat
      [ "call and return to" <+> PP.viaShow next
      , PP.indent 2 (PP.pretty s) ]
    PLTStub regs addr sym ->
      PP.vcat
      [ "call_via_got" <+> PP.viaShow sym <+> "(at" <+> PP.viaShow addr PP.<> ")"
      , PP.indent 2 (ppRegMap regs) ]
    ParsedJump s addr ->
      PP.vcat
      [ "jump" <+> PP.viaShow addr
      , PP.indent 2 (PP.pretty s) ]
    ParsedBranch r c t f  ->
      PP.vcat
      [ "branch" <+> PP.pretty c <+> PP.viaShow t <+> PP.viaShow f
      , PP.indent 2 (PP.pretty r) ]
    ParsedLookupTable _layout s idx entries ->
      PP.vcat
      [ "ijump" <+> PP.pretty idx
      , PP.indent 2 (PP.vcat (CL.imap (\i v -> PP.pretty i <+> ":->" <+> PP.viaShow v)
                             (V.toList entries)))
      , PP.indent 2 (PP.pretty s) ]
    ParsedReturn s ->
      PP.vcat
      [ "return"
      , PP.indent 2 (PP.pretty s) ]
    ParsedArchTermStmt ts s maddr ->
      PP.vcat
      [ ppArchTermStmt PP.pretty ts <> addrDoc
      , PP.indent 2 (PP.pretty s) ]
      where
          addrDoc = case maddr of
                      Just a -> ", return to" <+> PP.viaShow a
                      Nothing -> ""
    ParsedTranslateError msg ->
      "translation error" <+> PP.pretty msg
    ClassifyFailure s rsns ->
      PP.vcat
      [ "classify failure"
      , PP.indent 2 (PP.pretty s)
      , PP.indent 2 (PP.vcat (PP.pretty <$> rsns)) ]

instance ArchConstraints arch => Show (ParsedTermStmt arch ids) where
  show = show . ppTermStmt

-- | Get all successor blocks for the given list of statements.
parsedTermSucc :: ParsedTermStmt arch ids -> [ArchSegmentOff arch]
parsedTermSucc ts = do
  case ts of
    ParsedCall _ (Just ret_addr) -> [ret_addr]
    ParsedCall _ Nothing -> []
    PLTStub{} -> []
    ParsedJump _ tgt -> [tgt]
    ParsedBranch _ _ t f -> [t,f]
    ParsedLookupTable _layout _ _ v -> V.toList v
    ParsedReturn{} -> []
    ParsedArchTermStmt _ _ ret -> maybeToList ret
    ParsedTranslateError{} -> []
    ClassifyFailure{} -> []

------------------------------------------------------------------------
-- ParsedBlock

-- | A contiguous region of instructions in memory.
data ParsedBlock arch ids
   = ParsedBlock { pblockAddr :: !(ArchSegmentOff arch)
                   -- ^ Address of region
                 , pblockPrecond :: !(Either String (ArchBlockPrecond arch))
                   -- ^ Architecture-specificic information assumed to
                   -- be true when jumping to this block, or error why this
                   -- information could not be obtained.
                 , blockSize :: !Int
                   -- ^ The size of the region of memory covered by this.
                 , blockReason :: !(BlockExploreReason (ArchAddrWidth arch))
                   -- ^ Reason that we marked this address as
                   -- the start of a basic block.
                 , blockAbstractState :: !(AbsBlockState (ArchReg arch))
                   -- ^ Abstract state prior to the execution of
                   -- this region.
                 , blockJumpBounds :: !(Jmp.InitJumpBounds arch)
                   -- ^ Structure for computing bounds on jump tables.
                 , pblockStmts :: ![Stmt arch ids]
                     -- ^ The non-terminal statements in the block
                 , pblockTermStmt  :: !(ParsedTermStmt arch ids)
                   -- ^ The terminal statement in the block.
                 }

deriving instance (ArchConstraints arch, Show (ArchBlockPrecond arch))
  => Show (ParsedBlock arch ids)

instance ArchConstraints arch
      => PP.Pretty (ParsedBlock arch ids) where
  pretty b =
    PP.vcat
    [ PP.viaShow (pblockAddr b) PP.<> ":"
    , PP.indent 2 (PP.vcat $ ("; " <+>) <$> Jmp.ppInitJumpBounds (blockJumpBounds b))
    , PP.indent 2 (PP.vcat [PP.vcat (ppStmt ppOff <$> pblockStmts b), ppTermStmt (pblockTermStmt b)])
    ]
    where ppOff o = PP.viaShow (incAddr (toInteger o) (segoffAddr (pblockAddr b)))

-- | Stores the main block features that may changes from parsing a block.
data ParsedContents arch ids =
  ParsedContents { parsedNonterm :: ![Stmt arch ids]
                   -- ^ The non-terminal statements in the block
                 , parsedTerm  :: !(ParsedTermStmt arch ids)
                   -- ^ The terminal statement in the block.
                 , writtenCodeAddrs :: ![ArchSegmentOff arch]
                 -- ^ Addresses marked executable that were written to memory.
                 , intraJumpTargets :: ![Jmp.IntraJumpTarget arch]
                 , newFunctionAddrs :: ![ArchSegmentOff arch]
                   -- ^ List of candidate functions found when parsing block.
                   --
                   -- Note. In a binary, these could denote the non-executable
                   -- segments, so they are filtered before traversing.
                 }
