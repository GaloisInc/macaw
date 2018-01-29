{-|
Copyright  : (c) Galois, Inc 2016-2018
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
  , StatementList(..)
  , ParsedBlock(..)
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
  , trustKnownFns
    -- * DiscoveryFunInfo
  , DiscoveryFunInfo(..)
  , parsedBlocks
    -- * CodeAddrRegion
  , CodeAddrReason(..)
    -- * DiscoveryState utilities
  , RegConstraint
  )  where

import           Control.Lens
import qualified Data.ByteString.Char8 as BSC
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
import           Data.Macaw.Types

------------------------------------------------------------------------
-- CodeAddrReason

-- | This describes the source of an address that was marked as containing code.
data CodeAddrReason w
   = InWrite !(MemSegmentOff w)
     -- ^ Exploring because the given block writes it to memory.
   | NextIP !(MemSegmentOff w)
     -- ^ Exploring because the given block jumps here.
   | CallTarget !(MemSegmentOff w)
     -- ^ Exploring because address terminates with a call that jumps here.
   | InitAddr
     -- ^ Identified as an entry point from initial information
   | CodePointerInMem !(MemSegmentOff w)
     -- ^ A code pointer that was stored at the given address.
   | SplitAt !(MemAddr w)
     -- ^ Added because the address split this block after it had been disassembled.
   | UserRequest
     -- ^ The user requested that we analyze this address as a function.
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

------------------------------------------------------------------------
-- ParsedTermStmt

-- | This term statement is used to describe higher level expressions
-- of how block ending with a a FetchAndExecute statement should be
-- interpreted.
data ParsedTermStmt arch ids
   = ParsedCall !(RegState (ArchReg arch) (Value arch ids))
                !(Maybe (ArchSegmentOff arch))
    -- ^ A call with the current register values and location to return to or 'Nothing'  if this is a tail call.
   | ParsedJump !(RegState (ArchReg arch) (Value arch ids)) !(ArchSegmentOff arch)
     -- ^ A jump to an explicit address within a function.
   | ParsedLookupTable !(RegState (ArchReg arch) (Value arch ids))
                       !(BVValue arch ids (ArchAddrWidth arch))
                       !(V.Vector (ArchSegmentOff arch))
     -- ^ A lookup table that branches to one of a vector of addresses.
     --
     -- The registers store the registers, the value contains the index to jump
     -- to, and the possible addresses as a table.  If the index (when interpreted as
     -- an unsigned number) is larger than the number of entries in the vector, then the
     -- result is undefined.
   | ParsedReturn !(RegState (ArchReg arch) (Value arch ids))
     -- ^ A return with the given registers.
   | ParsedIte !(Value arch ids BoolType) !(StatementList arch ids) !(StatementList arch ids)
     -- ^ An if-then-else
   | ParsedArchTermStmt !(ArchTermStmt arch ids)
                        !(RegState (ArchReg arch) (Value arch ids))
                        !(Maybe (ArchSegmentOff arch))
     -- ^ An architecture-specific statement with the registers prior to execution, and
     -- the given next control flow address.
   | ParsedTranslateError !Text
     -- ^ An error occured in translating the block
   | ClassifyFailure !(RegState (ArchReg arch) (Value arch ids))
     -- ^ The classifier failed to identity the block.

-- | Pretty print the block contents indented inside brackets.
ppStatementList :: ArchConstraints arch => (ArchAddrWord arch -> Doc) -> StatementList arch ids -> Doc
ppStatementList ppOff b =
  text "{" <$$>
  indent 2 (vcat (ppStmt ppOff  <$> stmtsNonterm b) <$$>
            ppTermStmt ppOff (stmtsTerm b)) <$$>
  text "}"

ppTermStmt :: ArchConstraints arch
           => (ArchAddrWord arch -> Doc)
              -- ^ Given an address offset, this prints the value
           -> ParsedTermStmt arch ids
           -> Doc
ppTermStmt ppOff tstmt =
  case tstmt of
    ParsedCall s Nothing ->
      text "tail call" <$$>
      indent 2 (pretty s)
    ParsedCall s (Just next) ->
      text "call and return to" <+> text (show next) <$$>
      indent 2 (pretty s)
    ParsedJump s addr ->
      text "jump" <+> text (show addr) <$$>
      indent 2 (pretty s)
    ParsedLookupTable s idx entries ->
      text "ijump" <+> pretty idx <$$>
      indent 2 (vcat (imap (\i v -> int i <+> text ":->" <+> text (show v))
                           (V.toList entries))) <$$>
      indent 2 (pretty s)
    ParsedReturn s ->
      text "return" <$$>
      indent 2 (pretty s)
    ParsedIte c t f ->
      text "ite" <+> pretty c <$$>
      ppStatementList ppOff t <$$>
      ppStatementList ppOff f
    ParsedArchTermStmt ts s maddr ->
      let addrDoc = case maddr of
                      Just a -> text ", return to" <+> text (show a)
                      Nothing -> text ""
       in prettyF ts <> addrDoc <$$>
          indent 2 (pretty s)
    ParsedTranslateError msg ->
      text "translation error" <+> text (Text.unpack msg)
    ClassifyFailure s ->
      text "unknown transfer" <$$>
      indent 2 (pretty s)

instance ArchConstraints arch => Show (ParsedTermStmt arch ids) where
  show = show . ppTermStmt (text . show)

------------------------------------------------------------------------
-- StatementList

-- | This is a code block after we have classified the control flow
-- statement(s) that the block ends with.
data StatementList arch ids
   = StatementList { stmtsIdent :: !Word64
                     -- ^ An index for uniquely identifying the block.
                     --
                     -- This is primarily used so that we can reference
                     -- which branch lead to a particular next state.
                   , stmtsNonterm :: !([Stmt arch ids])
                     -- ^ The non-terminal statements in the block
                   , stmtsTerm  :: !(ParsedTermStmt arch ids)
                     -- ^ The terminal statement in the block.
                   , stmtsAbsState :: !(AbsProcessorState (ArchReg arch) ids)
                     -- ^ The abstract state of the block just before terminal
                   }

deriving instance ArchConstraints arch
  => Show (StatementList arch ids)

------------------------------------------------------------------------
-- ParsedBlock

-- | A contiguous region of instructions in memory.
data ParsedBlock arch ids
   = ParsedBlock { pblockAddr :: !(ArchSegmentOff arch)
                   -- ^ Address of region
                 , blockSize :: !(ArchAddrWord arch)
                   -- ^ The size of the region of memory covered by this.
                 , blockReason :: !(CodeAddrReason (ArchAddrWidth arch))
                   -- ^ Reason that we marked this address as
                   -- the start of a basic block.
                 , blockAbstractState :: !(AbsBlockState (ArchReg arch))
                   -- ^ Abstract state prior to the execution of
                   -- this region.
                 , blockStatementList :: !(StatementList arch ids)
                   -- ^ Returns the entry block for the region
                 }

deriving instance ArchConstraints arch
  => Show (ParsedBlock arch ids)

instance ArchConstraints arch
      => Pretty (ParsedBlock arch ids) where
  pretty b =
    let sl = blockStatementList b
        ppOff o = text (show (incAddr (toInteger o) (relativeSegmentAddr (pblockAddr b))))
     in text (show (pblockAddr b)) PP.<> text ":" <$$>
        indent 2 (vcat (ppStmt ppOff <$> stmtsNonterm sl) <$$> ppTermStmt ppOff (stmtsTerm sl))

------------------------------------------------------------------------
-- DiscoveryFunInfo

-- | Information discovered about a particular function
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunAddr :: !(ArchSegmentOff arch)
                        -- ^ Address of function entry block.
                      , discoveredFunName :: !BSC.ByteString
                        -- ^ Name of function should be unique for program
                      , _parsedBlocks :: !(Map (ArchSegmentOff arch) (ParsedBlock arch ids))
                        -- ^ Maps an address to the blocks associated with that address.
                      }

parsedBlocks :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentOff arch) (ParsedBlock arch ids))
parsedBlocks = lens _parsedBlocks (\s v -> s { _parsedBlocks = v })

instance ArchConstraints arch => Pretty (DiscoveryFunInfo arch ids) where
  pretty info =
    text "function" <+> text (BSC.unpack (discoveredFunName info)) <$$>
    vcat (pretty <$> Map.elems (info^.parsedBlocks))

------------------------------------------------------------------------
-- DiscoveryState

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
                   , _unexploredFunctions :: !(Map (ArchSegmentOff arch) (CodeAddrReason (ArchAddrWidth arch)))
                     -- ^ This maps addresses that have been marked as
                     -- functions, but not yet analyzed to the reason
                     -- they are analyzed.
                     --
                     -- The keys in this map and `_funInfo` should be mutually disjoint.
                   , _trustKnownFns       :: !Bool
                     -- ^ Should we use and depend on known function entries in
                     -- our analysis? E.g. used to distinguish jumps vs. tail calls
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
                    -> AddrSymMap (ArchAddrWidth arch)
                       -- ^ Map from addresses
                    -> ArchitectureInfo arch
                       -- ^ architecture/OS specific information
                    -> DiscoveryState arch
emptyDiscoveryState mem symbols info =
  DiscoveryState
  { memory               = mem
  , symbolNames          = symbols
  , archInfo             = info
  , _globalDataMap       = Map.empty
  , _funInfo             = Map.empty
  , _unexploredFunctions = Map.empty
  , _trustKnownFns       = False
  }

-- | Map each jump table start to the address just after the end.
globalDataMap :: Simple Lens (DiscoveryState arch)
                             (Map (ArchMemAddr arch) (GlobalDataInfo (ArchMemAddr arch)))
globalDataMap = lens _globalDataMap (\s v -> s { _globalDataMap = v })

-- | List of functions to explore next.
unexploredFunctions :: Simple Lens (DiscoveryState arch)
                              (Map (ArchSegmentOff arch) (CodeAddrReason (ArchAddrWidth arch)))
unexploredFunctions = lens _unexploredFunctions (\s v -> s { _unexploredFunctions = v })

-- | Get information for specific functions
funInfo :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentOff arch) (Some (DiscoveryFunInfo arch)))
funInfo = lens _funInfo (\s v -> s { _funInfo = v })

trustKnownFns :: Simple Lens (DiscoveryState arch) Bool
trustKnownFns = lens _trustKnownFns (\s v -> s { _trustKnownFns = v })

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Constraint on architecture register values needed by code exploration.
type RegConstraint r = (OrdF r, HasRepr r TypeRepr, RegisterInfo r, ShowF r)
