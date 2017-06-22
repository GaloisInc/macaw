{-|
Copyright  : (c) Galois, Inc 2016-2017
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
  ( GlobalDataInfo(..)
  , ParsedTermStmt(..)
  , ParsedBlock(..)
  , ParsedBlockRegion(..)
     -- * SymbolAddrMap
  , SymbolAddrMap
  , emptySymbolAddrMap
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
  , DiscoveryFunInfo(..)
  , parsedBlocks
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
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
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
   | UserRequest
     -- ^ The user requested that we analyze this address as a function.
  deriving (Show)

------------------------------------------------------------------------
-- SymbolAddrMap

-- | Map from addresses to the associated symbol name.
newtype SymbolAddrMap w = SymbolAddrMap { symbolAddrsAsMap :: Map (SegmentedAddr w) BSC.ByteString }

-- | Return an empty symbol addr map
emptySymbolAddrMap :: SymbolAddrMap w
emptySymbolAddrMap = SymbolAddrMap Map.empty

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
   | ParsedIte !(Value arch ids BoolType) !(ParsedBlock arch ids) !(ParsedBlock arch ids)
     -- ^ An if-then-else
   | ParsedSyscall !(RegState (ArchReg arch) (Value arch ids))
                   !(ArchSegmentedAddr arch)
     -- ^ A system call with the registers prior to call and given return address.
   | ParsedTranslateError !Text
     -- ^ An error occured in translating the block
   | ClassifyFailure !(RegState (ArchReg arch) (Value arch ids))
     -- ^ The classifier failed to identity the block.

deriving instance ArchConstraints arch => Show (ParsedTermStmt arch ids)

-- | Pretty print the block contents indented inside brackets.
ppBlockIndented :: ArchConstraints arch => ParsedBlock arch ids -> Doc
ppBlockIndented b =
  text "{" <$$>
  indent 2 (vcat (pretty <$> pblockStmts b) <$$> pretty (pblockTerm b)) <$$>
  text "}"

instance ArchConstraints arch => Pretty (ParsedTermStmt arch ids) where
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
  pretty (ParsedIte c t f) =
    text "ite" <+> pretty c <$$>
    ppBlockIndented t <$$>
    ppBlockIndented f
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

-- | This is a code block after we have classified the control flow
-- statement(s) that the block ends with.
data ParsedBlock arch ids
   = ParsedBlock { pblockLabel :: !Word64
                   -- ^ An index for uniquely identifying the block.
                   --
                   -- This is primarily used so that we can reference
                   -- which branch lead to a particular next state.
                 , pblockStmts :: !([Stmt arch ids])
                   -- ^ The non-terminal statements in the block
                 , pblockTerm  :: !(ParsedTermStmt arch ids)
                   -- ^ The terminal statement in the block.
                 }

deriving instance ArchConstraints arch
  => Show (ParsedBlock arch ids)

------------------------------------------------------------------------
-- ParsedBlockRegion

-- | A contiguous region of instructions in memory.
data ParsedBlockRegion arch ids
   = ParsedBlockRegion { regionAddr :: !(ArchSegmentedAddr arch)
                         -- ^ Address of region
                       , regionSize :: !(ArchAddr arch)
                         -- ^ The size of the region of memory covered by this.
                       , regionReason :: !(CodeAddrReason (ArchAddrWidth arch))
                          -- ^ Reason that we marked this address as
                          -- the start of a basic block.
                       , regionAbstractState :: !(AbsBlockState (ArchReg arch))
                         -- ^ Abstract state prior to the execution of
                         -- this region.
                       , regionFirstBlock :: !(ParsedBlock arch ids)
                         -- ^ Returns the entry block for the region
                       }

deriving instance ArchConstraints arch
  => Show (ParsedBlockRegion arch ids)

instance ArchConstraints arch
      => Pretty (ParsedBlockRegion arch ids) where
  pretty r =
    let b = regionFirstBlock r
     in text (show (regionAddr r)) PP.<> text ":" <$$>
        indent 2 (vcat (pretty <$> pblockStmts b) <$$> pretty (pblockTerm b))

------------------------------------------------------------------------
-- DiscoveryFunInfo

-- | Information discovered about a particular function
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunAddr :: !(ArchSegmentedAddr arch)
                        -- ^ Address of function entry block.
                      , discoveredFunName :: !BSC.ByteString
                        -- ^ Name of function should be unique for program
                      , _parsedBlocks :: !(Map (ArchSegmentedAddr arch) (ParsedBlockRegion arch ids))
                        -- ^ Maps an address to the blocks associated with that address.
                      }

parsedBlocks :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentedAddr arch) (ParsedBlockRegion arch ids))
parsedBlocks = lens _parsedBlocks (\s v -> s { _parsedBlocks = v })

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
                   , _funInfo :: !(Map (ArchSegmentedAddr arch) (Some (DiscoveryFunInfo arch)))
                     -- ^ Map from function addresses to discovered information about function
                   , _unexploredFunctions :: !(Map (ArchSegmentedAddr arch) (CodeAddrReason (ArchAddrWidth arch)))
                     -- ^ This maps addresses that have been marked as
                     -- functions, but not yet analyzed to the reason
                     -- they are analyzed.
                     --
                     -- The keys in this map and `_funInfo` should be mutually disjoint.
                   }

-- | Return list of all functions discovered so far.
exploredFunctions :: DiscoveryState arch -> [Some (DiscoveryFunInfo arch)]
exploredFunctions i = Map.elems $ i^.funInfo

withDiscoveryArchConstraints :: DiscoveryState arch
                             -> (ArchConstraints arch => a)
                             -> a
withDiscoveryArchConstraints dinfo = withArchConstraints (archInfo dinfo)

ppDiscoveryStateBlocks :: DiscoveryState arch
                      -> Doc
ppDiscoveryStateBlocks info = withDiscoveryArchConstraints info $
    vcat $ f <$> Map.elems (info^.funInfo)
  where f :: ArchConstraints arch => Some (DiscoveryFunInfo arch) -> Doc
        f (Some v) = pretty v

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
  , _funInfo             = Map.empty
  , _unexploredFunctions = Map.empty
  }

-- | Map each jump table start to the address just after the end.
globalDataMap :: Simple Lens (DiscoveryState arch)
                             (Map (ArchSegmentedAddr arch)
                                  (GlobalDataInfo (ArchSegmentedAddr arch)))
globalDataMap = lens _globalDataMap (\s v -> s { _globalDataMap = v })

-- | List of functions to explore next.
unexploredFunctions :: Simple Lens (DiscoveryState arch)
                              (Map (ArchSegmentedAddr arch) (CodeAddrReason (ArchAddrWidth arch)))
unexploredFunctions = lens _unexploredFunctions (\s v -> s { _unexploredFunctions = v })

-- | Get information for specific functions
funInfo :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentedAddr arch) (Some (DiscoveryFunInfo arch)))
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
asLiteralAddr _ (RelocatableValue _ i) = Just i
asLiteralAddr _ _ = Nothing
