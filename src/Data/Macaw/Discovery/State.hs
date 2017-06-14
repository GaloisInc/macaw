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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.Discovery.State
  ( lookupParsedBlock
  , GlobalDataInfo(..)
  , ParsedTermStmt(..)
  , ParsedBlock(..)
  , ParsedBlockRegion(..)
     -- * SymbolAddrMap
  , SymbolAddrMap
  , symbolAddrsAsMap
  , symbolAddrMap
  , symbolAddrs
  , symbolAtAddr
    -- * The interpreter state
  , DiscoveryState
  , exploredFunctions
  , ppDiscoveryStateBlocks
  , emptyDiscoveryState
  , memory
  , symbolNames
  , archInfo
  , globalDataMap
  , funInfo
  , unexploredFunctions
    -- * DiscoveryFunInfo
  , DiscoveryFunInfo
  , initDiscoveryFunInfo
  , discoveredFunAddr
  , discoveredFunName
  , FoundAddr(..)
  , foundAddrs
  , parsedBlocks
  , reverseEdges
    -- * CodeAddrRegion
  , CodeAddrReason(..)
    -- ** DiscoveryState utilities
  , RegConstraint
  , asLiteralAddr
  )  where

import           Control.Lens
import qualified Data.ByteString.Char8 as BSC
import           Data.Char (isDigit)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Set (Set)
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
-- FoundAddr

-- | An address that has been found to be reachable.
data FoundAddr arch
   = FoundAddr { foundReason :: !(CodeAddrReason (ArchAddrWidth arch))
                 -- ^ The reason the address was found to be containing code.
               , foundAbstractState :: !(AbsBlockState (ArchReg arch))
                 -- ^ The abstract state formed from post-states that reach this address.
               }

------------------------------------------------------------------------
-- SymbolAddrMap

-- | Map from addresses to the associated symbol name.
newtype SymbolAddrMap w = SymbolAddrMap { symbolAddrsAsMap :: Map (SegmentedAddr w) BSC.ByteString }

-- | Return addresses in symbol name map
symbolAddrs :: SymbolAddrMap w -> [SegmentedAddr w]
symbolAddrs = Map.keys . symbolAddrsAsMap

-- | Return the symbol at the given map.
symbolAtAddr :: SegmentedAddr w -> SymbolAddrMap w -> Maybe BSC.ByteString
symbolAtAddr a m = Map.lookup a (symbolAddrsAsMap m)

-- | Check that a symbol name is well formed, returning an error message if not.
checkSymbolName :: BSC.ByteString -> Either String ()
checkSymbolName sym_nm =
  case BSC.unpack sym_nm of
    [] -> Left "Empty symbol name"
    (c:_) | isDigit c -> Left "Symbol name that starts with a digit."
          | otherwise -> Right ()

-- | This creates a symbol addr map after checking the correctness of
-- symbol names.
--
-- It returns either an error message or the map.
symbolAddrMap :: forall w
              .  Map (SegmentedAddr w) BSC.ByteString
              -> Either String (SymbolAddrMap w)
{-
symbolAddrMap symbols
  | Map.size symbol_names /= Map.size symbols = do
      let l = filter isMulti (Map.toList symbol_names)
       in Left $ "Duplicate symbol names in symbol name map:\n" ++ show l
  where symbol_names :: Map BSC.ByteString [SegmentedAddr w]
        symbol_names = foldl insPair Map.empty (Map.toList symbols)

        isMulti :: (BSC.ByteString, [SegmentedAddr w])
                -> Bool
        isMulti (_,[_]) = False
        isMulti (_,_)   = True

        insPair :: Map BSC.ByteString [SegmentedAddr w]
                -> (SegmentedAddr w, BSC.ByteString)
                -> Map BSC.ByteString [SegmentedAddr w]
        insPair m (a,nm) = Map.insertWith (++) nm [a] m
-}
symbolAddrMap symbols = do
   mapM_ checkSymbolName (Map.elems symbols)
   pure $! SymbolAddrMap symbols

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

deriving instance ArchConstraints arch => Show (ParsedTermStmt arch ids)

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

deriving instance ArchConstraints arch
  => Show (ParsedBlock arch ids)


ppParsedBlock :: ArchConstraints arch
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
deriving instance ArchConstraints arch
  => Show (ParsedBlockRegion arch ids)

instance ArchConstraints arch
      => Pretty (ParsedBlockRegion arch ids) where
  pretty r = vcat $ ppParsedBlock (regionAddr r) <$> Map.elems (regionBlockMap r)

------------------------------------------------------------------------
-- DiscoveryFunInfo

type ReverseEdgeMap arch = Map (ArchSegmentedAddr arch) (Set (ArchSegmentedAddr arch))

-- | Information discovered about a particular function
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunAddr :: !(ArchSegmentedAddr arch)
                        -- ^ Address of function entry block.
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

-- | Does a simple lookup in the cfg at a given DecompiledBlock address.
lookupParsedBlock :: DiscoveryFunInfo arch ids
                  -> ArchLabel arch
                  -> Maybe (ParsedBlock arch ids)
lookupParsedBlock info lbl = do
  br <- Map.lookup (labelAddr lbl) (info^.parsedBlocks)
  Map.lookup (labelIndex lbl) (regionBlockMap br)

initDiscoveryFunInfo :: ArchitectureInfo arch
                        -- ^ Architecture information
                     -> Memory (ArchAddrWidth arch)
                        -- ^ Contents of memory for initializing abstract state.
                     -> SymbolAddrMap (ArchAddrWidth arch)
                        -- ^ The symbol map for computing the name
                     -> ArchSegmentedAddr arch
                        -- ^ Address of this function
                     -> CodeAddrReason (ArchAddrWidth arch)
                        -- ^ Reason this function was discovered
                     -> DiscoveryFunInfo arch ids
initDiscoveryFunInfo info mem symMap addr rsn =
  let nm = fromMaybe (BSC.pack (show addr)) (symbolAtAddr addr symMap)
      faddr = FoundAddr { foundReason = rsn
                        , foundAbstractState = mkInitialAbsState info mem addr
                        }
   in DiscoveryFunInfo { discoveredFunAddr = addr
                       , discoveredFunName = nm
                       , _foundAddrs = Map.singleton addr faddr
                       , _parsedBlocks = Map.empty
                       , _reverseEdges = Map.empty
                       }

instance ArchConstraints arch => Pretty (DiscoveryFunInfo arch ids) where
  pretty info =
    text "function" <+> text (BSC.unpack (discoveredFunName info)) <$$>
    vcat (pretty <$> Map.elems (info^.parsedBlocks))

------------------------------------------------------------------------
-- DiscoveryState



-- | Information discovered about the program
data DiscoveryState arch
   = DiscoveryState { memory      :: !(Memory (ArchAddrWidth arch))
                     -- ^ The initial memory when disassembly started.
                   , symbolNames :: !(SymbolAddrMap (ArchAddrWidth arch))
                     -- ^ Map addresses to known symbol names
                   , archInfo    :: !(ArchitectureInfo arch)
                     -- ^ Architecture-specific information needed for discovery.
                   , _globalDataMap :: !(Map (ArchSegmentedAddr arch)
                                             (GlobalDataInfo (ArchSegmentedAddr arch)))
                     -- ^ Maps each address that appears to be global data to information
                     -- inferred about it.
                   , _funInfo :: !(Map (ArchSegmentedAddr arch) (Maybe (Some (DiscoveryFunInfo arch))))
                     -- ^ Map from function addresses to discovered information about function
                     --
                     -- If the binding is bound value has been explored it is a DiscoveryFunInfo.  If it
                     -- has been discovered and added to the unexploredFunctions below, then it is bound to
                     -- 'Nothing'.
                   , _unexploredFunctions :: ![(ArchSegmentedAddr arch, CodeAddrReason (ArchAddrWidth arch))]
                     -- ^ A list of addresses that we have marked as function entries, but not yet
                     -- explored.
                   }

-- | Return list of all functions discovered so far.
exploredFunctions :: DiscoveryState arch -> [Some (DiscoveryFunInfo arch)]
exploredFunctions i = mapMaybe id $ Map.elems $ i^.funInfo

withDiscoveryArchConstraints :: DiscoveryState arch
                             -> (ArchConstraints arch => a)
                             -> a
withDiscoveryArchConstraints dinfo = withArchConstraints (archInfo dinfo)

ppDiscoveryStateBlocks :: DiscoveryState arch
                      -> Doc
ppDiscoveryStateBlocks info = withDiscoveryArchConstraints info $
    vcat $ f <$> Map.elems (info^.funInfo)
  where f :: ArchConstraints arch => Maybe (Some (DiscoveryFunInfo arch)) -> Doc
        f (Just (Some v)) = pretty v
        f Nothing = PP.empty

-- | Create empty discovery information.
emptyDiscoveryState :: Memory (ArchAddrWidth arch)
                       -- ^ State of memory
                    -> SymbolAddrMap (ArchAddrWidth arch)
                       -- ^ Map from addresses
                    -> ArchitectureInfo arch
                       -- ^ architecture/OS specific information
                    -> DiscoveryState arch
emptyDiscoveryState mem symbols info =
  DiscoveryState
  { memory             = mem
  , symbolNames        = symbols
  , archInfo           = info
  , _globalDataMap     = Map.empty
  , _funInfo           = Map.empty
  , _unexploredFunctions = []
  }

-- | Map each jump table start to the address just after the end.
globalDataMap :: Simple Lens (DiscoveryState arch)
                             (Map (ArchSegmentedAddr arch)
                                  (GlobalDataInfo (ArchSegmentedAddr arch)))
globalDataMap = lens _globalDataMap (\s v -> s { _globalDataMap = v })

-- | List of functions to explore next.
unexploredFunctions :: Simple Lens (DiscoveryState arch)
                                 [(ArchSegmentedAddr arch, CodeAddrReason (ArchAddrWidth arch))]
unexploredFunctions = lens _unexploredFunctions (\s v -> s { _unexploredFunctions = v })

-- | Get information for specific functions
funInfo :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentedAddr arch) (Maybe (Some (DiscoveryFunInfo arch))))
funInfo = lens _funInfo (\s v -> s { _funInfo = v })

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Constraint on architecture register values needed by code exploration.
type RegConstraint r = (OrdF r, HasRepr r TypeRepr, RegisterInfo r, ShowF r)

-- | This returns a segmented address if the value can be interpreted as a literal memory
-- address, and returns nothing otherwise.
asLiteralAddr :: MemWidth (ArchAddrWidth arch)
              => Memory (ArchAddrWidth arch)
              -> BVValue arch ids (ArchAddrWidth arch)
              -> Maybe (ArchSegmentedAddr arch)
asLiteralAddr mem (BVValue _ val) =
  absoluteAddrSegment mem (fromInteger val)
asLiteralAddr mem (RelocatableValue _ i) =
  absoluteAddrSegment mem (fromIntegral i)
asLiteralAddr _ _ = Nothing
