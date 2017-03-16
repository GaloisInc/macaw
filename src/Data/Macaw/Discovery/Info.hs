{-|
Copyright  : (c) Galois, Inc 2016
Maintainer : jhendrix@galois.com

This defines the main data structure for storing information learned from code
discovery.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.Discovery.Info
  ( BlockRegion(..)
  , FoundAddr(..)
  , lookupParsedBlock
  , GlobalDataInfo(..)
  , ParsedTermStmt(..)
  , ParsedBlock(..)
  , ParsedBlockRegion(..)
    -- * The interpreter state
  , DiscoveryInfo
  , ppDiscoveryInfoBlocks

  , emptyDiscoveryInfo
  , nonceGen
  , memory
  , symbolNames
  , archInfo

  , globalDataMap

  , functionEntries
  , funInfo
  , function_frontier

    -- * DiscoveryFunInfo
  , DiscoveryFunInfo
  , initDiscoveryFunInfo
  , discoveredFunName
  , foundAddrs
  , parsedBlocks
  , reverseEdges
    -- * CodeAddrRegion
  , CodeAddrReason(..)
    -- ** DiscoveryInfo utilities
  , ArchConstraint
  , asLiteralAddr
  , tryGetStaticSyscallNo
  )  where

import           Control.Lens
import           Control.Monad.ST
import qualified Data.ByteString.Char8 as BSC
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe)
import           Data.Parameterized.Classes
import           Data.Parameterized.Nonce
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.AbsDomain.AbsState
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.Memory
import           Data.Macaw.Types


------------------------------------------------------------------------
-- FoundAddr

-- | An address that has been found to be reachable.
data FoundAddr arch
   = FoundAddr { foundReason :: !(CodeAddrReason (ArchAddrWidth arch))
                 -- ^ The reason the address was found to be containing code.
               , foundAbstractState :: !(AbsBlockState (ArchReg arch))
                 -- ^ The abstract state formed from post-states that reach this address.
               }

------------------------------------------------------------------------
-- BlockRegion

-- | A contiguous region of instructions in memory.
data BlockRegion arch ids
   = BlockRegion { brSize :: !(ArchAddr arch)
                   -- ^ The size of the region of memory covered by this.
                 , brBlocks :: !(Map Word64 (Block arch ids))
                   -- ^ Map from labelIndex to associated block.
                 }

------------------------------------------------------------------------
-- CodeAddrReason

-- | This describes the source of an address that was marked as containing code.
data CodeAddrReason w
   = InWrite !(SegmentedAddr w)
     -- ^ Exploring because the given block writes it to memory.
   | NextIP !(SegmentedAddr w)
     -- ^ Exploring because the given block jumps here.
   | CallTarget !(SegmentedAddr w)
     -- ^ Exploring because address terminates with a call that jumps here.
   | InitAddr
     -- ^ Identified as an entry point from initial information
   | CodePointerInMem !(SegmentedAddr w)
     -- ^ A code pointer that was stored at the given address.
   | SplitAt !(SegmentedAddr w)
     -- ^ Added because the address split this block after it had been disassembled.
   | InterProcedureJump !(SegmentedAddr w)
     -- ^ A jump from an address in another function.
  deriving (Show)

------------------------------------------------------------------------
-- GlobalDataInfo

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

------------------------------------------------------------------------
-- ParsedTermStmt

-- | This term statement is used to describe higher level expressions
-- of how block ending with a a FetchAndExecute statement should be
-- interpreted.
data ParsedTermStmt arch ids
   = ParsedCall !(RegState (ArchReg arch) (Value arch ids))
                !(Maybe (ArchSegmentedAddr arch))
    -- ^ A call with the current register values and location to return to or 'Nothing'  if this is a tail call.
   | ParsedJump !(RegState (ArchReg arch) (Value arch ids)) !(ArchSegmentedAddr arch)
     -- ^ A jump to an explicit address within a function.
   | ParsedLookupTable !(RegState (ArchReg arch) (Value arch ids))
                       !(BVValue arch ids (ArchAddrWidth arch))
                       !(V.Vector (ArchSegmentedAddr arch))
     -- ^ A lookup table that branches to one of a vector of addresses.
     --
     -- The registers store the registers, the value contains the index to jump
     -- to, and the possible addresses.
   | ParsedReturn !(RegState (ArchReg arch) (Value arch ids))
     -- ^ A return with the given registers.
   | ParsedBranch !(Value arch ids BoolType) !Word64 !Word64
     -- ^ A branch (i.e., BlockTerm is Branch)
   | ParsedSyscall !(RegState (ArchReg arch) (Value arch ids))
                   !(ArchSegmentedAddr arch)
     -- ^ A system call with the registers prior to call and given return address.
   | ParsedTranslateError !Text
     -- ^ An error occured in translating the block
   | ClassifyFailure !(RegState (ArchReg arch) (Value arch ids))
     -- ^ The classifier failed to identity the block.

deriving instance
  ( PrettyCFGConstraints arch
  , Show (ArchReg arch (BVType (ArchAddrWidth arch)))
  )
  => Show (ParsedTermStmt arch ids)

instance (OrdF (ArchReg arch), ShowF (ArchReg arch)) => Pretty (ParsedTermStmt arch ids) where
  pretty (ParsedCall s Nothing) =
    text "tail call" <$$>
    indent 2 (pretty s)
  pretty (ParsedCall s (Just next)) =
    text "call and return to" <+> text (show next) <$$>
    indent 2 (pretty s)
  pretty (ParsedJump s addr) =
    text "jump" <+> text (show addr) <$$>
    indent 2 (pretty s)
  pretty (ParsedLookupTable s idx entries) =
    text "ijump" <+> pretty idx <$$>
    indent 2 (vcat (imap (\i v -> int i <+> text ":->" <+> text (show v)) (V.toList entries))) <$$>
    indent 2 (pretty s)
  pretty (ParsedReturn s) =
    text "return" <$$>
    indent 2 (pretty s)
  pretty (ParsedBranch c t f) =
    text "branch" <+> pretty c <+> text (show t) <+> text (show f)
  pretty (ParsedSyscall s addr) =
    text "syscall, return to" <+> text (show addr) <$$>
    indent 2 (pretty s)
  pretty (ParsedTranslateError msg) =
    text "translation error" <+> text (Text.unpack msg)
  pretty (ClassifyFailure s) =
    text "unknown transfer" <$$>
    indent 2 (pretty s)

------------------------------------------------------------------------
-- ParsedBlock

data ParsedBlock arch ids
   = ParsedBlock { pblockLabel :: !Word64
                 , pblockStmts :: !([Stmt arch ids])
                 , pblockState :: !(AbsProcessorState (ArchReg arch) ids)
                   -- ^ State of processor prior to term statement.
                 , pblockTerm  :: !(ParsedTermStmt arch ids)
                 }

deriving instance (PrettyCFGConstraints arch
                  , Show (ArchReg arch (BVType (ArchAddrWidth arch)))
                  )
  => Show (ParsedBlock arch ids)


ppParsedBlock :: (PrettyArch arch,  OrdF (ArchReg arch))
              => ArchSegmentedAddr arch
              -> ParsedBlock arch ids
              -> Doc
ppParsedBlock a b =
  pretty (GeneratedBlock a (pblockLabel b)) PP.<> text ":" <$$>
  indent 2 (vcat (pretty <$> pblockStmts b) <$$>
            pretty (pblockTerm b))

------------------------------------------------------------------------
-- ParsedBlockRegion

-- | A contiguous region of instructions in memory.
data ParsedBlockRegion arch ids
   = ParsedBlockRegion { regionAddr :: !(ArchSegmentedAddr arch)
                       , regionSize :: !(ArchAddr arch)
                       -- ^ The size of the region of memory covered by this.
                       , regionBlockMap :: !(Map Word64 (ParsedBlock arch ids))
                       -- ^ Map from labelIndex to associated block.
                       }
deriving instance (PrettyCFGConstraints arch
                  , Show (ArchReg arch (BVType (ArchAddrWidth arch)))
                  )
  => Show (ParsedBlockRegion arch ids)

instance (OrdF (ArchReg arch), PrettyArch arch)
      => Pretty (ParsedBlockRegion arch ids) where
  pretty r = vcat $ ppParsedBlock (regionAddr r) <$> Map.elems (regionBlockMap r)

------------------------------------------------------------------------
-- DiscoveryFunInfo

type ReverseEdgeMap arch = (Map (ArchSegmentedAddr arch) (Set (ArchSegmentedAddr arch)))

-- | Information discovered about a particular
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunAddr :: !(ArchSegmentedAddr arch)
                      , discoveredFunName :: !BSC.ByteString
                        -- ^ Name of function should be unique for program
                      , _foundAddrs :: !(Map (ArchSegmentedAddr arch) (FoundAddr arch))
                        -- ^ Maps fopund address to the pre-state for that block.
                      , _parsedBlocks :: !(Map (ArchSegmentedAddr arch) (ParsedBlockRegion arch ids))
                        -- ^ Maps an address to the blocks associated with that address.
                      , _reverseEdges :: !(ReverseEdgeMap arch)
                       -- ^ Maps each code address to the list of predecessors that
                       -- affected its abstract state.
                      }

foundAddrs :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentedAddr arch) (FoundAddr arch))
foundAddrs = lens _foundAddrs (\s v -> s { _foundAddrs = v })

parsedBlocks :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentedAddr arch) (ParsedBlockRegion arch ids))
parsedBlocks = lens _parsedBlocks (\s v -> s { _parsedBlocks = v })

reverseEdges :: Simple Lens (DiscoveryFunInfo arch ids) (ReverseEdgeMap arch)
reverseEdges = lens _reverseEdges (\s v -> s { _reverseEdges = v })

initDiscoveryFunInfo :: ArchitectureInfo arch
                        -- ^ Architecture information
                     -> Memory (ArchAddrWidth arch)
                        -- ^ Contents of memory for initializing abstract state.
                     -> Map (ArchSegmentedAddr arch) BSC.ByteString
                        -- ^ The symbol map for computing the name
                     -> ArchSegmentedAddr arch
                        -- ^ Address of this function
                     -> CodeAddrReason (ArchAddrWidth arch)
                        -- ^ Reason this function was discovered
                     -> DiscoveryFunInfo arch ids
initDiscoveryFunInfo info mem symMap addr rsn =
  let nm = fromMaybe (BSC.pack (show addr)) (Map.lookup addr symMap)
      faddr = FoundAddr { foundReason = rsn
                        , foundAbstractState = fnBlockStateFn info mem addr
                        }
   in DiscoveryFunInfo { discoveredFunAddr = addr
                       , discoveredFunName = nm
                       , _foundAddrs = Map.singleton addr faddr
                       , _parsedBlocks = Map.empty
                       , _reverseEdges = Map.empty
                       }

instance (OrdF (ArchReg arch), PrettyArch arch) => Pretty (DiscoveryFunInfo arch ids) where
  pretty info =
    text "function" <+> text (BSC.unpack (discoveredFunName info)) <$$>
    vcat (pretty <$> Map.elems (info^.parsedBlocks))

------------------------------------------------------------------------
-- DiscoveryInfo

-- | Information discovered about the program
data DiscoveryInfo arch ids
   = DiscoveryInfo { nonceGen    :: !(NonceGenerator (ST ids) ids)
                     -- ^ Generator for creating fresh ids.
                   , memory      :: !(Memory (ArchAddrWidth arch))
                     -- ^ The initial memory when disassembly started.
                   , symbolNames :: !(Map (ArchSegmentedAddr arch) BSC.ByteString)
                     -- ^ Map addresses to known symbol names
                   , archInfo    :: !(ArchitectureInfo arch)
                     -- ^ Architecture-specific information needed for discovery.
                   , _globalDataMap :: !(Map (ArchSegmentedAddr arch)
                                             (GlobalDataInfo (ArchSegmentedAddr arch)))
                     -- ^ Maps each address that appears to be global data to information
                     -- inferred about it.

                   , _functionEntries :: !(Set (ArchSegmentedAddr arch))
                      -- ^ Maps addresses that are marked as the start of a function
                   , _funInfo :: !(Map (ArchSegmentedAddr arch) (DiscoveryFunInfo arch ids))
                     -- ^ Map from function addresses to discovered information about function

                   , _function_frontier :: !(Map (ArchSegmentedAddr arch)
                                                 (CodeAddrReason (ArchAddrWidth arch)))
                     -- ^ Set of functions to explore next.
                   }

ppDiscoveryInfoBlocks :: (OrdF (ArchReg arch), PrettyArch arch)
                      => DiscoveryInfo arch ids -> Doc
ppDiscoveryInfoBlocks info = vcat (pretty <$> Map.elems (info^.funInfo))

-- | Empty interpreter state.
emptyDiscoveryInfo :: NonceGenerator (ST ids) ids
                   -> Memory (ArchAddrWidth arch)
                   -> Map (ArchSegmentedAddr arch) BSC.ByteString
                   -> ArchitectureInfo arch
                      -- ^ architecture/OS specific information
                   -> DiscoveryInfo arch ids
emptyDiscoveryInfo ng mem symbols info =
  DiscoveryInfo
      { nonceGen           = ng
      , memory             = mem
      , symbolNames        = symbols
      , archInfo           = info
      , _globalDataMap     = Map.empty

      , _functionEntries   = Set.empty
      , _funInfo           = Map.empty
      , _function_frontier = Map.empty
      }


-- | Map each jump table start to the address just after the end.
globalDataMap :: Simple Lens (DiscoveryInfo arch ids)
                             (Map (ArchSegmentedAddr arch)
                                  (GlobalDataInfo (ArchSegmentedAddr arch)))
globalDataMap = lens _globalDataMap (\s v -> s { _globalDataMap = v })

-- | Set of functions to explore next.
function_frontier :: Simple Lens (DiscoveryInfo arch ids)
                                 (Map (ArchSegmentedAddr arch)
                                      (CodeAddrReason (ArchAddrWidth arch)))
function_frontier = lens _function_frontier (\s v -> s { _function_frontier = v })


-- | Get information for specific functions
funInfo :: Simple Lens (DiscoveryInfo arch ids) (Map (ArchSegmentedAddr arch) (DiscoveryFunInfo arch ids))
funInfo = lens _funInfo (\s v -> s { _funInfo = v })

-- | Addresses that start each function.
functionEntries :: Simple Lens (DiscoveryInfo arch ids) (Set (ArchSegmentedAddr arch))
functionEntries = lens _functionEntries (\s v -> s { _functionEntries = v })

-- | Does a simple lookup in the cfg at a given DecompiledBlock address.
lookupParsedBlock :: DiscoveryFunInfo arch ids
                  -> ArchLabel arch
                  -> Maybe (ParsedBlock arch ids)
lookupParsedBlock info lbl = do
  br <- Map.lookup (labelAddr lbl) (info^.parsedBlocks)
  Map.lookup (labelIndex lbl) (regionBlockMap br)

------------------------------------------------------------------------
-- DiscoveryInfo utilities

-- | Constraint on architecture register values needed by code exploration.
type RegConstraint r = (OrdF r, HasRepr r TypeRepr, RegisterInfo r, ShowF r)

-- | Constraint on architecture so that we can do code exploration.
type ArchConstraint a ids = ( RegConstraint (ArchReg a)
                            )

-- | This returns a segmented address if the value can be interpreted as a literal memory
-- address, and returns nothing otherwise.
asLiteralAddr :: MemWidth (ArchAddrWidth arch)
              => Memory (ArchAddrWidth arch)
              -> BVValue arch ids (ArchAddrWidth arch)
              -> Maybe (ArchSegmentedAddr arch)
asLiteralAddr mem (BVValue _ val) =
  absoluteAddrSegment mem (fromInteger val)
asLiteralAddr _   (RelocatableValue _ a) = Just a
asLiteralAddr _ _ = Nothing

tryGetStaticSyscallNo :: ArchConstraint arch ids
                      => DiscoveryFunInfo arch ids
                         -- ^ Discovery information about a function
                      -> ArchSegmentedAddr arch
                         -- ^ Address of this block
                      -> RegState (ArchReg arch) (Value arch ids)
                         -- ^ State of processor
                      -> Maybe Integer
tryGetStaticSyscallNo interp_state block_addr proc_state
  | BVValue _ call_no <- proc_state^.boundValue syscall_num_reg =
    Just call_no
  | Initial r <- proc_state^.boundValue syscall_num_reg
  , Just info <- interp_state^.foundAddrs^.at block_addr =
    asConcreteSingleton (foundAbstractState info^.absRegState^.boundValue r)
  | otherwise =
    Nothing
