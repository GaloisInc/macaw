{-|
This defines the data structures for storing information learned from
code discovery.  The 'DiscoveryState' is the main data structure
representing this information.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
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
  , UnexploredFunctionMap
  , unexploredFunctions
  , Info.NoReturnFunStatus(..)
  , trustedFunctionEntryPoints
  , exploreFnPred
    -- * DiscoveryFunInfo
  , DiscoveryFunInfo(..)
  , discoveredFunName
  , parsedBlocks
    -- ** Parsed block
  , Parsed.ParsedBlock(..)
    -- ** Block terminal statements
  , Parsed.ParsedTermStmt(..)
  , Parsed.parsedTermSucc
    -- ** JumpTableLayout
  , Parsed.JumpTableLayout(..)
  , Parsed.Extension(..)
  , Parsed.jtlBackingAddr
  , Parsed.jtlBackingSize
    -- * BoundedMemArray
  , Parsed.BoundedMemArray(..)
  , Parsed.arByteCount
  , Parsed.isReadOnlyBoundedMemArray
    -- * Reasons for exploring
  , FunctionExploreReason(..)
  , ppFunReason
  , Parsed.BlockExploreReason(..)
    -- * DiscoveryState utilities
  , RegConstraint
  , setArchInfo
  )  where

import           Control.Lens
import qualified Data.ByteString.Char8 as BSC
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Numeric (showHex)
import           Prettyprinter as PP

import           Data.Macaw.Architecture.Info as Info
import           Data.Macaw.CFG
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
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
-- DiscoveryFunInfo

-- | Information discovered about a particular function
data DiscoveryFunInfo arch ids
   = DiscoveryFunInfo { discoveredFunReason :: !(FunctionExploreReason (ArchAddrWidth arch))
                      , discoveredFunAddr :: !(ArchSegmentOff arch)
                        -- ^ Address of function entry block.
                      , discoveredFunSymbol :: !(Maybe BSC.ByteString)
                        -- ^ A symbol associated with the definition.
                      , _parsedBlocks :: !(Map (ArchSegmentOff arch) (Parsed.ParsedBlock arch ids))
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

parsedBlocks :: Simple Lens (DiscoveryFunInfo arch ids) (Map (ArchSegmentOff arch) (Parsed.ParsedBlock arch ids))
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
                    , _trustedFunctionEntryPoints :: !(Map (ArchSegmentOff arch) Info.NoReturnFunStatus)
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

-- | modify the archInfo
setArchInfo ::
  ArchitectureInfo arch ->
  DiscoveryState arch ->
  DiscoveryState arch
setArchInfo ainfo st = st { archInfo = ainfo }


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
  , _trustedFunctionEntryPoints = Info.MayReturnFun <$ addrSymMap
  , _exploreFnPred       = const True
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
  :: Simple Lens (DiscoveryState arch) (Map (ArchSegmentOff arch) Info.NoReturnFunStatus)
trustedFunctionEntryPoints =
  lens _trustedFunctionEntryPoints (\s v -> s { _trustedFunctionEntryPoints = v })

exploreFnPred :: Simple Lens (DiscoveryState arch) (ArchSegmentOff arch -> Bool)
exploreFnPred = lens _exploreFnPred (\s v -> s { _exploreFnPred = v })

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Constraint on architecture register values needed by code exploration.
type RegConstraint r = (OrdF r, HasRepr r TypeRepr, RegisterInfo r, ShowF r)
