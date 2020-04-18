{-|
This defines the data structures for storing information learned from
code discovery.  The 'DiscoveryState' is the main data structure
representing this information.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Discovery.State
  ( -- * DiscoveryState
    DiscoveryState
  , AddrSymMap
  , exploredFunctions
  , ppDiscoveryStateBlocks
  , emptyDiscoveryState
  , memory
  , symbolNames
  , archInfo
  , GlobalDataInfo(..)
  , globalDataMap
  , funInfo
  , unexploredFunctions
  , NoReturnFunStatus(..)
  , trustedFunctionEntryPoints
  , exploreFnPred
    -- * DiscoveryFunInfo
  , DiscoveryFunInfo(..)
  , discoveredFunName
  , parsedBlocks
    -- ** Parsed block
  , ParsedBlock(..)
    -- ** Block terminal statements
  , ParsedTermStmt(..)
  , parsedTermSucc
    -- ** JumpTableLayout
  , JumpTableLayout(..)
  , Extension(..)
  , jtlBackingAddr
  , jtlBackingSize
    -- * BoundedMemArray
  , BoundedMemArray(..)
  , arByteCount
  , isReadOnlyBoundedMemArray
    -- * Reasons for exploring
  , FunctionExploreReason(..)
  , ppFunReason
  , BlockExploreReason(..)
    -- * DiscoveryState utilities
  , RegConstraint
  )  where

import           Control.Lens
import qualified Data.ByteString.Char8 as BSC
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (maybeToList)
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Text (Text)
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Prettyprinter as PP

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

------------------------------------------------------------------------
-- AddrSymMap

-- | Maps code addresses to the associated symbol name if any.
type AddrSymMap w = Map.Map (MemSegmentOff w) BSC.ByteString

------------------------------------------------------------------------
-- BlockExploreReason

-- | This describes why we started exploring a given function.
data FunctionExploreReason w
     -- | Exploring because code at the given block writes it to memory.
  = PossibleWriteEntry !(MemSegmentOff w)
    -- | Exploring because address terminates with a call that jumps here.
  | CallTarget !(MemSegmentOff w)
    -- | Identified as an entry point from initial information
  | InitAddr
    -- | A code pointer that was stored at the given address.
  | CodePointerInMem !(MemSegmentOff w)
    -- | The user requested that we analyze this address as a function.
  | UserRequest
  deriving (Eq, Show)

-- | Print exploration reason.
ppFunReason :: FunctionExploreReason w -> String
ppFunReason rsn =
  case rsn of
    InitAddr -> ""
    UserRequest -> ""
    PossibleWriteEntry a -> " (written at " ++ showHex (memWordValue (addrOffset (segoffAddr a))) ")"
    CallTarget a -> " (called at " ++ showHex (memWordValue (addrOffset (segoffAddr a))) ")"
    CodePointerInMem a -> " (in initial memory at " ++ showHex (memWordValue (addrOffset (segoffAddr a))) ")"

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

------------------------------------------------------------------------
-- GlobalDataInfo

-- | Information about a region of memory.
data GlobalDataInfo w
  -- | A jump table that appears to end just before the given address.
  = JumpTable !(Maybe w)
  -- | A value that appears in the program text.
  | ReferencedValue

instance (Integral w, Show w) => Show (GlobalDataInfo w) where
  show (JumpTable Nothing) = "unbound jump table"
  show (JumpTable (Just w)) | w >= 0 = "jump table end " ++ showHex w ""
                            | otherwise = error "jump table with negative offset given"
  show ReferencedValue = "global addr"

-------------------------------------------------------------------------------
-- BoundedMemArray

-- | This describes a region of memory dereferenced in some array read.
--
-- These regions may be be sparse, given an index `i`, the
-- the address given by 'arBase' + 'arIx'*'arStride'.
data BoundedMemArray arch tp = BoundedMemArray
  { arBase   :: !(MemSegmentOff (ArchAddrWidth arch))
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
  -- ^ `AbsoluteJumpTable r` describes a jump table where the jump
  -- target is directly stored in the array read `r`.
  | forall w . RelativeJumpTable !(ArchSegmentOff arch)
                                 !(BoundedMemArray arch (BVType w))
                                 !(Extension w)
  -- ^ `RelativeJumpTable base read ext` describes information about a
  -- jump table where all jump targets are relative to a fixed base
  -- address.
  --
  -- The value is computed as `baseVal + readVal` where
  --
  -- `baseVal = fromMaybe 0 base`, `readVal` is the value stored at
  -- the memory read described by `read` with the sign of `ext`.

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
  -- branch that jumps to `trueAddr` if `cond` is true and `falseAddr` otherwise.
  --
  -- The value assigned to the IP in `regs` should reflect this if-then-else
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
  | ParsedArchTermStmt !(ArchTermStmt arch ids)
                       !(RegState (ArchReg arch) (Value arch ids))
                       !(Maybe (ArchSegmentOff arch))
  -- | An error occured in translating the block
  | ParsedTranslateError !Text
  -- | The classifier failed to identity the block.
  -- Includes registers with list of reasons for each classifer to fail
  | ClassifyFailure !(RegState (ArchReg arch) (Value arch ids)) [String]

ppTermStmt :: ArchConstraints arch
           => ParsedTermStmt arch ids
           -> Doc ann
ppTermStmt tstmt =
  case tstmt of
    ParsedCall s Nothing ->
      vcat
      [ "tail_call"
      , indent 2 (pretty s) ]
    ParsedCall s (Just next) ->
      vcat
      [ "call and return to" <+> viaShow next
      , indent 2 (pretty s) ]
    PLTStub regs addr sym ->
      vcat
      [ "call_via_got" <+> viaShow sym <+> "(at" <+> viaShow addr PP.<> ")"
      , indent 2 (ppRegMap regs) ]
    ParsedJump s addr ->
      vcat
      [ "jump" <+> viaShow addr
      , indent 2 (pretty s) ]
    ParsedBranch r c t f  ->
      vcat
      [ "branch" <+> pretty c <+> viaShow t <+> viaShow f
      , indent 2 (pretty r) ]
    ParsedLookupTable _layout s idx entries ->
      vcat
      [ "ijump" <+> pretty idx
      , indent 2 (vcat (imap (\i v -> pretty i <+> ":->" <+> viaShow v)
                             (V.toList entries)))
      , indent 2 (pretty s) ]
    ParsedReturn s ->
      vcat
      [ "return"
      , indent 2 (pretty s) ]
    ParsedArchTermStmt ts s maddr ->
      vcat
      [ prettyF ts <> addrDoc
      , indent 2 (pretty s) ]
      where
          addrDoc = case maddr of
                      Just a -> ", return to" <+> viaShow a
                      Nothing -> ""
    ParsedTranslateError msg ->
      "translation error" <+> pretty msg
    ClassifyFailure s rsns ->
      vcat
      [ "classify failure"
      , indent 2 (pretty s)
      , indent 2 (vcat (pretty <$> rsns)) ]

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
                 , pblockStmts :: !([Stmt arch ids])
                     -- ^ The non-terminal statements in the block
                 , pblockTermStmt  :: !(ParsedTermStmt arch ids)
                   -- ^ The terminal statement in the block.
                 }

deriving instance (ArchConstraints arch, Show (ArchBlockPrecond arch))
  => Show (ParsedBlock arch ids)

instance ArchConstraints arch
      => Pretty (ParsedBlock arch ids) where
  pretty b =
    vcat
    [ viaShow (pblockAddr b) PP.<> ":"
    , indent 2 (vcat $ ("; " <+>) <$> Jmp.ppInitJumpBounds (blockJumpBounds b))
    , indent 2 (vcat [vcat (ppStmt ppOff <$> pblockStmts b), ppTermStmt (pblockTermStmt b)])
    ]
    where ppOff o = viaShow (incAddr (toInteger o) (segoffAddr (pblockAddr b)))

------------------------------------------------------------------------
-- DiscoveryFunInfo

-- | Information discovered about a particular function
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunReason :: !(FunctionExploreReason (ArchAddrWidth arch))
                      , discoveredFunAddr :: !(ArchSegmentOff arch)
                        -- ^ Address of function entry block.
                      , discoveredFunSymbol :: !(Maybe BSC.ByteString)
                        -- ^ A symbol associated with the definition.
                      , _parsedBlocks :: !(Map (ArchSegmentOff arch) (ParsedBlock arch ids))
                        -- ^ Maps the start addresses of function blocks to their contents
                      , discoveredClassifyFailureResolutions :: [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                        -- ^ A side mapping that records jump targets for
                        -- 'ClassifyFailure' block terminators that have been
                        -- gleaned from an external source.  When interpreting
                        -- the function, this map can be used to complete the
                        -- control flow of functions with 'ClassifyFailure's.
                      }

-- | Returns the "name" associated with a function.
--
-- This is either the symbol or the address.
discoveredFunName :: MemWidth (ArchAddrWidth arch)
                  => DiscoveryFunInfo arch ids
                  -> BSC.ByteString
discoveredFunName finfo =
  case discoveredFunSymbol finfo of
    Just nm -> nm
    Nothing -> BSC.pack (show (discoveredFunAddr finfo))

parsedBlocks :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentOff arch) (ParsedBlock arch ids))
parsedBlocks = lens _parsedBlocks (\s v -> s { _parsedBlocks = v })

instance ArchConstraints arch => Pretty (DiscoveryFunInfo arch ids) where
  pretty info =
    vcat
    [ "function" <+> nm
    , vcat (pretty <$> Map.elems (info^.parsedBlocks)) ]
    where
        addr = viaShow (discoveredFunAddr info)
        nm = case discoveredFunSymbol info of
               Just sym -> pretty (BSC.unpack sym) <+> "@" <+> addr
               Nothing -> addr

------------------------------------------------------------------------
-- NoReturnFunStatus

-- | Flags whether a function is labeled no return or not.
data NoReturnFunStatus
   = NoReturnFun
     -- ^ Function labeled no return
   | MayReturnFun
     -- ^ Function may retun

------------------------------------------------------------------------
-- DiscoveryState

type UnexploredFunctionMap arch =
  Map (ArchSegmentOff arch) (FunctionExploreReason (ArchAddrWidth arch))

-- | Information discovered about the program
data DiscoveryState arch
   = DiscoveryState { memory              :: !(Memory (ArchAddrWidth arch))
                      -- ^ The initial memory when disassembly started.
                    , symbolNames          :: !(AddrSymMap (ArchAddrWidth arch))
                      -- ^ Map addresses to known symbol names
                    , archInfo             :: !(ArchitectureInfo arch)
                      -- ^ Architecture-specific information needed for discovery.
                    , _globalDataMap       :: !(Map (ArchMemAddr arch)
                                                (GlobalDataInfo (ArchMemAddr arch)))
                      -- ^ Maps each address that appears to be global data to information
                      -- inferred about it.
                    , _funInfo             :: !(Map (ArchSegmentOff arch) (Some (DiscoveryFunInfo arch)))
                      -- ^ Map from function addresses to discovered information about function
                    , _unexploredFunctions
                      :: !(UnexploredFunctionMap arch)
                      -- ^ This maps addresses that have been marked as
                      -- functions, but not yet analyzed to the reason
                      -- they are analyzed.
                      --
                      -- The keys in this map and `_funInfo` should be mutually disjoint.
                    , _trustedFunctionEntryPoints :: !(Map (ArchSegmentOff arch) NoReturnFunStatus)
                      -- ^ This is the set of addresses that we treat
                      -- as definitely belonging to function entry
                      -- points.
                      --
                      -- The discovery process will not allow
                      -- intra-procedural jumps to these addresses.
                      -- Jumps to these addresses must either be calls
                      -- or tail calls.
                      --
                      -- To ensure translation is invariant on the
                      -- order in which functions are visited, this
                      -- set should be initialized upfront, and not
                      -- changed.
                    , _exploreFnPred :: !(ArchSegmentOff arch -> Bool)
                      -- ^ This predicate decides whether to explore a
                      -- function at the given address or not.
                    }

-- | Return list of all functions discovered so far.
exploredFunctions :: DiscoveryState arch -> [Some (DiscoveryFunInfo arch)]
exploredFunctions i = Map.elems $ i^.funInfo

withDiscoveryArchConstraints :: DiscoveryState arch
                             -> (ArchConstraints arch => a)
                             -> a
withDiscoveryArchConstraints dinfo = withArchConstraints (archInfo dinfo)

ppDiscoveryStateBlocks :: DiscoveryState arch -> Doc ann
ppDiscoveryStateBlocks info = withDiscoveryArchConstraints info $
    vcat $ f <$> Map.elems (info^.funInfo)
  where f :: ArchConstraints arch => Some (DiscoveryFunInfo arch) -> Doc ann
        f (Some v) = pretty v

-- | Create empty discovery information.
emptyDiscoveryState :: Memory (ArchAddrWidth arch)
                       -- ^ State of memory
                    -> AddrSymMap (ArchAddrWidth arch)
                       -- ^ Map from addresses to their symbol name (if any)
                    -> ArchitectureInfo arch
                       -- ^ architecture/OS specific information
                    -> DiscoveryState arch
emptyDiscoveryState mem addrSymMap info =
  DiscoveryState
  { memory               = mem
  , symbolNames          = addrSymMap
  , archInfo             = info
  , _globalDataMap       = Map.empty
  , _funInfo             = Map.empty
  , _unexploredFunctions = Map.empty
  , _trustedFunctionEntryPoints = fmap (\_ -> MayReturnFun) addrSymMap
  , _exploreFnPred       = \_ -> True
  }

-- | Map each jump table start to the address just after the end.
globalDataMap :: Lens' (DiscoveryState arch)
                      (Map (ArchMemAddr arch) (GlobalDataInfo (ArchMemAddr arch)))
globalDataMap = lens _globalDataMap (\s v -> s { _globalDataMap = v })

-- | List of functions to explore next.
unexploredFunctions
  :: Simple Lens (DiscoveryState arch) (UnexploredFunctionMap arch)
unexploredFunctions = lens _unexploredFunctions (\s v -> s { _unexploredFunctions = v })

-- | Get information for specific functions
funInfo :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentOff arch) (Some (DiscoveryFunInfo arch)))
funInfo = lens _funInfo (\s v -> s { _funInfo = v })

-- | Retrieves functions that are trusted entry points.
trustedFunctionEntryPoints
  :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentOff arch) NoReturnFunStatus)
trustedFunctionEntryPoints =
  lens _trustedFunctionEntryPoints (\s v -> s { _trustedFunctionEntryPoints = v })

exploreFnPred :: Simple Lens (DiscoveryState arch) (ArchSegmentOff arch -> Bool)
exploreFnPred = lens _exploreFnPred (\s v -> s { _exploreFnPred = v })

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Constraint on architecture register values needed by code exploration.
type RegConstraint r = (OrdF r, HasRepr r TypeRepr, RegisterInfo r, ShowF r)
