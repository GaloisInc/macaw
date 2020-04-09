{- |
Copyright        : (c) Galois, Inc 2015-2019
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This module discovers the Functions and their internal Block CFG in
target binaries.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Discovery
       ( -- * DiscoveryInfo
         State.DiscoveryState(..)
       , State.emptyDiscoveryState
       , State.trustedFunctionEntryPoints
       , State.AddrSymMap
       , State.funInfo
       , State.exploredFunctions
       , State.ppDiscoveryStateBlocks
       , State.unexploredFunctions
       , Data.Macaw.Discovery.cfgFromAddrs
       , Data.Macaw.Discovery.cfgFromAddrsAndState
       , Data.Macaw.Discovery.markAddrsAsFunction
       , State.FunctionExploreReason(..)
       , State.BlockExploreReason(..)
       , Data.Macaw.Discovery.analyzeFunction
       , Data.Macaw.Discovery.exploreMemPointers
       , Data.Macaw.Discovery.analyzeDiscoveredFunctions
       , Data.Macaw.Discovery.addDiscoveredFunctionBlockTargets
         -- * Top level utilities
       , Data.Macaw.Discovery.completeDiscoveryState
       , DiscoveryOptions(..)
       , defaultDiscoveryOptions
       , DiscoveryEvent(..)
       , discoveryLogFn
         -- * DiscoveryFunInfo
       , State.DiscoveryFunInfo
       , State.discoveredFunAddr
       , State.discoveredFunName
       , State.discoveredClassifyFailureResolutions
       , State.parsedBlocks
         -- * Parsed block
       , State.ParsedBlock
       , State.pblockAddr
       , State.blockSize
       , State.blockReason
       , State.blockAbstractState
       , State.pblockStmts
       , State.pblockTermStmt
       , State.ParsedTermStmt(..)
         -- * Simplification
       , eliminateDeadStmts
       ) where

import           Control.Applicative
import           Control.Lens
import qualified Control.Monad.Fail as Fail
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Monoid
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V
import           GHC.IO (ioToST)
import           Numeric.Natural
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen (pretty)

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.AbsDomain.Refine
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
import           Data.Macaw.CFG.Rewriter
import           Data.Macaw.DebugLogging
import           Data.Macaw.Discovery.AbsEval
import           Data.Macaw.Discovery.State as State
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

#define USE_REWRITER 1

------------------------------------------------------------------------
-- Utilities

isExecutableSegOff :: MemSegmentOff w -> Bool
isExecutableSegOff sa =
  segmentFlags (segoffSegment sa) `Perm.hasPerm` Perm.execute

-- | Get code pointers out of a abstract value.
identifyConcreteAddresses :: MemWidth w
                          => Memory w
                          -> AbsValue w (BVType w)
                          -> [MemSegmentOff w]
identifyConcreteAddresses mem (FinSet s) =
  mapMaybe (resolveAbsoluteAddr mem . fromInteger) (Set.toList s)
identifyConcreteAddresses _ (CodePointers s _) = Set.toList s
identifyConcreteAddresses _mem StridedInterval{} = []
identifyConcreteAddresses _mem _ = []

{-
-- | Return true if this address was added because of the contents of a global address
-- in memory initially.
--
-- This heuristic is not very accurate, so we avoid printing errors when it leads to
-- issues.
cameFromUnsoundReason :: Map (ArchMemAddr arch) (FoundAddr arch)
                      -> CodeAddrReason (ArchAddrWidth arch)
                      -> Bool
cameFromUnsoundReason found_map rsn = do
  let prev addr =
        case Map.lookup addr found_map of
          Just info -> cameFromUnsoundReason found_map (foundReason info)
          Nothing -> error $ "Unknown reason for address " ++ show addr
  case rsn of
    InWrite{} -> True
    NextIP src  -> prev src
    CallTarget src -> prev src
    SplitAt src -> prev src
    InitAddr -> False
    CodePointerInMem{} -> True
-}

------------------------------------------------------------------------
--


------------------------------------------------------------------------
-- Eliminate dead code in blocks

-- | Add any values needed to compute term statement to demand set.
addTermDemands :: TermStmt arch ids -> DemandComp arch ids ()
addTermDemands t =
  case t of
    FetchAndExecute regs -> do
      traverseF_ addValueDemands regs
    TranslateError regs _ -> do
      traverseF_ addValueDemands regs
    ArchTermStmt _ regs -> do
      traverseF_ addValueDemands regs

-- | Add any assignments needed to evaluate statements with side
-- effects and terminal statement to demand set.
addBlockDemands :: Block arch ids -> DemandComp arch ids ()
addBlockDemands b = do
  mapM_ addStmtDemands (blockStmts b)
  addTermDemands (blockTerm b)

-- | Return a block after filtering out statements not needed to compute it.
elimDeadStmtsInBlock :: AssignIdSet ids -> Block arch ids -> Block arch ids
elimDeadStmtsInBlock demandSet b =
  b { blockStmts = filter (stmtNeeded demandSet) (blockStmts b)
    }

-- | Eliminate all dead statements in blocks
eliminateDeadStmts :: ArchitectureInfo arch -> Block arch ids -> Block arch ids
eliminateDeadStmts ainfo b = elimDeadStmtsInBlock demandSet b
  where demandSet =
          runDemandComp (archDemandContext ainfo) $ do
            addBlockDemands b

------------------------------------------------------------------------
-- Eliminate dead code in blocks

-- | Add any assignments needed to evaluate statements with side
-- effects and terminal statement to demand set.
addParsedBlockDemands :: ParsedBlock arch ids -> DemandComp arch ids ()
addParsedBlockDemands b = do
  mapM_ addStmtDemands (pblockStmts b)
  case pblockTermStmt b of
    ParsedCall regs _ -> do
      traverseF_ addValueDemands regs
    PLTStub regs _ _ ->
      traverseF_ addValueDemands regs
    ParsedJump regs _ -> do
      traverseF_ addValueDemands regs
    ParsedBranch regs _ _ _ -> do
      traverseF_ addValueDemands regs
    ParsedLookupTable regs _idx _tbl  -> do
      traverseF_ addValueDemands regs
    ParsedReturn regs -> do
      traverseF_ addValueDemands regs
    ParsedArchTermStmt _ regs _ -> do
      traverseF_ addValueDemands regs
    ParsedTranslateError _ -> do
      pure ()
    ClassifyFailure regs _ -> do
      traverseF_ addValueDemands regs

-- | Eliminate all dead statements in blocks
dropUnusedCodeInParsedBlock :: ArchitectureInfo arch
                            -> ParsedBlock arch ids
                            -> ParsedBlock arch ids
dropUnusedCodeInParsedBlock ainfo b =
    -- Important to force the result list here, since otherwise we
    -- hold onto the entire input list
    foldr seq () stmts' `seq` b { pblockStmts = stmts' }
  where stmts' = filter stmtPred (pblockStmts b)
        demandSet =
          runDemandComp (archDemandContext ainfo) $ do
            addParsedBlockDemands b
        stmtPred = stmtNeeded demandSet

------------------------------------------------------------------------
-- Memory utilities

sliceMemContents'
  :: MemWidth w
  => Int -- ^ Number of bytes in each slice.
  -> [[MemChunk w]] -- ^ Previous slices
  -> Integer -- ^ Number of slices to return
  -> [MemChunk w] -- ^ Ranges to process next
  -> Either (SplitError w) ([[MemChunk w]],[MemChunk w])
sliceMemContents' stride prev c next
  | c <= 0 = pure (reverse prev, next)
  | otherwise =
    case splitMemChunks next stride of
      Left e -> Left e
      Right (this, rest) -> sliceMemContents' stride (this:prev) (c-1) rest

-- | `sliceMemContents stride cnt contents` splits contents up into `cnt`
-- memory regions each with size `stride`.
sliceMemContents
  :: MemWidth w
  => Int -- ^ Number of bytes in each slice.
  -> Integer -- ^ Number of slices to return
  -> [MemChunk w] -- ^ Ranges to process next
  -> Either (SplitError w) ([[MemChunk w]],[MemChunk w])
sliceMemContents stride c next = sliceMemContents' stride [] c next

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Mark a escaped code pointer as a function entry.
markAddrAsFunction :: FunctionExploreReason (ArchAddrWidth arch)
                      -- ^ Information about why the code address was discovered
                      --
                      -- Used for debugging
                   -> ArchSegmentOff arch
                   -> DiscoveryState arch
                   -> DiscoveryState arch
markAddrAsFunction rsn addr s
  -- Do nothing if function is already explored.
  | Map.member addr (s^.funInfo) || Map.member addr (s^.unexploredFunctions) = s
  -- Ignore if address is not in an executable segment.
  | not (isExecutableSegOff addr) = s
  | otherwise = addrWidthClass (memAddrWidth (memory s)) $
    -- We check that the function address ignores bytes so that we do
    -- not start disassembling at a relocation or BSS region.
    case segoffContentsAfter addr of
      Right (ByteRegion _:_) ->
        s & unexploredFunctions %~ Map.insert addr rsn
      _ -> s

-- | Mark a list of addresses as function entries with the same reason.
markAddrsAsFunction :: Foldable t
                    => FunctionExploreReason (ArchAddrWidth arch)
                    -> t (ArchSegmentOff arch)
                    -> DiscoveryState arch
                    -> DiscoveryState arch
markAddrsAsFunction rsn addrs s0 =
  foldl' (\s a -> markAddrAsFunction rsn a s) s0 addrs

------------------------------------------------------------------------
-- FoundAddr

-- | An address that has been found to be reachable.
data FoundAddr arch
   = FoundAddr { foundReason :: !(BlockExploreReason (ArchAddrWidth arch))
                 -- ^ The reason the address was found to be containing code.
               , foundAbstractState :: !(AbsBlockState (ArchReg arch))
                 -- ^ The abstract state formed from post-states that reach this address.
               , foundJumpBounds :: !(Jmp.InitJumpBounds arch)
                 -- ^ The abstract state formed from post-states that reach this address
                 --
                 -- This is used for jump bounds.
               }

foundReasonL :: Lens' (FoundAddr arch) (BlockExploreReason (ArchAddrWidth arch))
foundReasonL = lens foundReason (\old new -> old { foundReason = new })

------------------------------------------------------------------------
-- FunState

-- | The state for the function exploration monad (funM)
data FunState arch s ids
   = FunState { funReason :: !(FunctionExploreReason (ArchAddrWidth arch))
              , funNonceGen  :: !(NonceGenerator (ST s) ids)
              , curFunAddr   :: !(ArchSegmentOff arch)
              , _curFunCtx   :: !(DiscoveryState arch)
                -- ^ Discovery state without this function
              , _curFunBlocks :: !(Map (ArchSegmentOff arch) (ParsedBlock arch ids))
                -- ^ Maps an address to the blocks associated with that address.
              , _foundAddrs :: !(Map (ArchSegmentOff arch) (FoundAddr arch))
                -- ^ Maps found address to the pre-state for that block.
              , _reverseEdges :: !(ReverseEdgeMap arch)
                -- ^ Maps each code address to the list of predecessors that
                -- affected its abstract state.
              , _frontier    :: !(Set (ArchSegmentOff arch))
                -- ^ Addresses to explore next.
              , classifyFailureResolutions :: [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                -- ^ The first element of each pair is the block (ending in a
                -- 'ClassifyFailure') for which the second element provides a
                -- list of known jump targets. These inform the initial
                -- frontier, but also need to be preserved as a side mapping
                -- when we construct the 'DiscoveryFunInfo'.
                --
                -- These resolutions are provided by external data (e.g.,
                -- another code discovery engine or SMT) and help resolve
                -- control flow that macaw cannot understand.
              }

-- | Discovery info
curFunCtx :: Simple Lens (FunState arch s ids)  (DiscoveryState arch)
curFunCtx = lens _curFunCtx (\s v -> s { _curFunCtx = v })

-- | Information about current function we are working on
curFunBlocks :: Simple Lens (FunState arch s ids) (Map (ArchSegmentOff arch) (ParsedBlock arch ids))
curFunBlocks = lens _curFunBlocks (\s v -> s { _curFunBlocks = v })

foundAddrs :: Simple Lens (FunState arch s ids) (Map (ArchSegmentOff arch) (FoundAddr arch))
foundAddrs = lens _foundAddrs (\s v -> s { _foundAddrs = v })

-- | Add a block to the current function blocks. If this overlaps with an
-- existing block, split them so that there's no overlap.
addFunBlock
  :: ArchSegmentOff arch
  -> ParsedBlock arch ids
  -> FunState arch s ids
  -> FunState arch s ids
addFunBlock segment block s = withArchConstraints (archInfo (s^.curFunCtx)) $
  case Map.lookupLT segment (s ^. curFunBlocks) of
    Just (bSegment, bBlock)
        -- very sneaky way to check that they are in the same segment (a
        -- Nothing result from diffSegmentOff will never be greater than a
        -- Just) and that they are overlapping (the block size is bigger than
        -- you'd expect given the address difference)
        | diffSegmentOff bSegment segment > Just (-toInteger (blockSize bBlock))
        -- put the overlapped segment back in the frontier
        -> s & curFunBlocks %~ (Map.insert segment block . Map.delete bSegment)
             & foundAddrs.at bSegment._Just.foundReasonL %~ SplitAt segment
             & frontier %~ Set.insert bSegment
    _ -> s & curFunBlocks %~ Map.insert segment block

type ReverseEdgeMap arch = Map (ArchSegmentOff arch) (Set (ArchSegmentOff arch))

-- | Maps each code address to the list of predecessors that
-- affected its abstract state.
reverseEdges :: Simple Lens (FunState arch s ids) (ReverseEdgeMap arch)
reverseEdges = lens _reverseEdges (\s v -> s { _reverseEdges = v })

-- | Set of addresses to explore next.
--
-- This is a map so that we can associate a reason why a code address
-- was added to the frontier.
frontier :: Simple Lens (FunState arch s ids) (Set (ArchSegmentOff arch))
frontier = lens _frontier (\s v -> s { _frontier = v })

------------------------------------------------------------------------
-- FunM

-- | A newtype around a function
newtype FunM arch s ids a = FunM { unFunM :: StateT (FunState arch s ids) (ST s) a }
  deriving (Functor, Applicative, Monad)

instance MonadState (FunState arch s ids) (FunM arch s ids) where
  get = FunM $ get
  put s = FunM $ put s

liftST :: ST s a -> FunM arch s ids a
liftST = FunM . lift

------------------------------------------------------------------------
-- Transfer functions

-- | Joins in the new abstract state and returns the locations for
-- which the new state is changed.
mergeIntraJump  :: ArchSegmentOff arch
                  -- ^ Source label that we are jumping from.
                -> IntraJumpTarget arch
                   -- ^ Target we are jumping to.
                -> FunM arch s ids ()
mergeIntraJump src (tgt, ab, bnds) = do
  info <- uses curFunCtx archInfo
  withArchConstraints info $ do
   when (not (absStackHasReturnAddr ab)) $ do
    debug DCFG ("WARNING: Missing return value in jump from " ++ show src ++ " to\n" ++ show ab) $
      pure ()
   -- Associate a new abstract state with the code region.
   foundMap <- use foundAddrs
   case Map.lookup tgt foundMap of
    -- We have seen this block before, so need to join and see if
    -- the results is changed.
    Just old_info -> do
      case joinAbsBlockState (foundAbstractState old_info) ab of
        Nothing  -> return ()
        Just new -> do
          let new_info = old_info { foundAbstractState = new }
          foundAddrs   %= Map.insert tgt new_info
          reverseEdges %= Map.insertWith Set.union tgt (Set.singleton src)
          frontier %= Set.insert tgt
    -- We haven't seen this block before
    Nothing -> do
      reverseEdges %= Map.insertWith Set.union tgt (Set.singleton src)
      frontier     %= Set.insert tgt
      let found_info = FoundAddr { foundReason = NextIP src
                                 , foundAbstractState = ab
                                 , foundJumpBounds = bnds
                                 }
      foundAddrs %= Map.insert tgt found_info

-------------------------------------------------------------------------------
-- BoundedMemArray

-- | This describes a region of memory dereferenced in some array read.
--
-- These regions may be be sparse, given an index `i`, the
-- the address given by 'arBase' + 'arIx'*'arStride'.
data BoundedMemArray arch tp = BoundedMemArray
  { arBase   :: !(MemSegmentOff (ArchAddrWidth arch))
    -- ^ The base address for array accesses.
  , arStride :: !Natural
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
    -- This could be computed from the previous fields, but we check we
    -- can create it when creating the array read, so we store it to
    -- avoid recomputing it.
  }

deriving instance RegisterInfo (ArchReg arch) => Show (BoundedMemArray arch tp)

-- | Return true if the address stored is readable and not writable.
isReadOnlyBoundedMemArray :: BoundedMemArray arch  tp -> Bool
isReadOnlyBoundedMemArray = Perm.isReadonly . segmentFlags . segoffSegment . arBase

absValueAsSegmentOff
  :: forall w
  .  Memory w
  -> AbsValue w (BVType  w)
  -> Maybe (MemSegmentOff w)
absValueAsSegmentOff mem av = case av of
  FinSet s | Set.size s == 1 -> resolveAbsoluteIntegerAddr (shead s)
  CodePointers s False | Set.size s == 1 -> Just (shead s)
  CodePointers s True  | Set.size s == 0 -> resolveAbsoluteIntegerAddr 0
  StridedInterval si -> SI.isSingleton si >>= resolveAbsoluteIntegerAddr
  _ -> Nothing
  where
  shead :: Set a -> a
  shead = Set.findMin

  resolveAbsoluteIntegerAddr :: Integer -> Maybe (MemSegmentOff w)
  resolveAbsoluteIntegerAddr = resolveAbsoluteAddr mem . addrWidthClass (memAddrWidth mem) fromInteger

-- | This attempts to interpret a value as a memory segment offset
-- using the memory and abstract interpretation of value.
valueAsSegmentOffWithTransfer
  :: forall arch ids
  .  RegisterInfo (ArchReg arch)
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> BVValue arch ids (ArchAddrWidth arch)
  -> Maybe (ArchSegmentOff arch)
valueAsSegmentOffWithTransfer mem aps base
  =   valueAsSegmentOff mem base
  <|> absValueAsSegmentOff mem (transferValue aps base)

-- | This attempts to pattern match a value as a memory address plus a value.
valueAsMemOffset
  :: RegisterInfo (ArchReg arch)
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> ArchAddrValue arch ids
  -> Maybe (ArchSegmentOff arch, ArchAddrValue arch ids)
valueAsMemOffset mem aps v
  | Just (BVAdd _ base offset) <- valueAsApp v
  , Just ptr <- valueAsSegmentOffWithTransfer mem aps base
  = Just (ptr, offset)

  -- and with the other argument order
  | Just (BVAdd _ offset base) <- valueAsApp v
  , Just ptr <- valueAsSegmentOffWithTransfer mem aps base
  = Just (ptr, offset)

  | otherwise = Nothing

-- | This operation extracts chunks of memory for a jump table.
extractJumpTableSlices :: ArchConstraints arch
                       => Jmp.IntraJumpBounds arch ids
                       -- ^ Bounds for jump table
                       -> MemSegmentOff (ArchAddrWidth arch) -- ^ Base address
                       -> Natural -- ^ Stride
                       -> BVValue arch ids idxWidth
                       -> MemRepr tp -- ^ Type of values
                       -> Classifier (V.Vector [MemChunk (ArchAddrWidth arch)])
extractJumpTableSlices jmpBounds base stride ixVal tp = do
  cnt <-
    case Jmp.unsignedUpperBound jmpBounds ixVal of
      Nothing -> fail $ "Upper bounds failed:\n"
                      ++ show (ppValueAssignments ixVal) ++ "\n"
                      ++ show (pretty jmpBounds)
      Just bnd -> do
        let cnt = toInteger (bnd+1)
        -- Check array actually fits in memory.
        when (cnt * toInteger stride > segoffBytesLeft base) $ do
          fail "Size is too large."
        pure cnt

  -- Get memory contents after base
  Right contents <- pure $ segoffContentsAfter base
  -- Break up contents into a list of slices each with size stide
  Right (strideSlices,_) <- pure $ sliceMemContents (fromIntegral stride) cnt contents
  -- Get memory slices
  Right slices <-
    pure $ traverse (\s -> fst <$> splitMemChunks s (fromIntegral (memReprBytes tp)))
                    (V.fromList strideSlices)
  pure slices

-- | See if the value can be interpreted as a read of memory
matchBoundedMemArray
  :: ArchConstraints arch
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> Jmp.IntraJumpBounds arch ids
     -- ^ Bounds for jump table
  -> BVValue arch ids w  -- ^ Value to interpret
  -> Classifier (BoundedMemArray arch (BVType w), ArchAddrValue arch ids)
matchBoundedMemArray mem aps jmpBounds val = do
  AssignedValue (Assignment _ (ReadMem addr tp)) <- pure val
  Just (base, offset) <- pure $ valueAsMemOffset mem aps addr
  Just (stride, ixVal) <- pure $ valueAsStaticMultiplication offset
   -- Check stride covers at least number of bytes read.
  when (memReprBytes tp > stride) $ do
    fail "Stride does not cover size of relocation."
  -- Resolve a static upper bound to array.

  -- Take the given number of bytes out of each slices
  slices <- extractJumpTableSlices jmpBounds base stride ixVal tp

  let r = BoundedMemArray
          { arBase     = base
          , arStride   = stride
          , arEltType  = tp
          , arSlices   = slices
          }
  pure  (r, ixVal)

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

-- | Just like Some (BVValue arch ids), but doesn't run into trouble with
-- partially applying the BVValue type synonym.
data SomeExt arch ids = forall m . SomeExt !(BVValue arch ids m) !(Extension m)

matchAddr :: NatRepr w -> Maybe (AddrWidthRepr w)
matchAddr w
  | Just Refl <- testEquality w n32 = Just Addr32
  | Just Refl <- testEquality w n64 = Just Addr64
  | otherwise = Nothing

-- | `matchExtension x` matches in `x` has the form `(uext y w)` or `(sext y w)` and returns
-- a description about the extension as well as the pattern `y`.
matchExtension :: forall arch ids
               .  ( MemWidth (ArchAddrWidth arch)
                  , HasRepr (ArchReg arch) TypeRepr)
               => ArchAddrValue arch ids
               -> SomeExt arch ids
matchExtension val =
  case valueAsApp val of
    Just (SExt val' _w) | Just repr <- matchAddr (typeWidth val') -> SomeExt val' (Extension True  repr)
    Just (UExt val' _w) | Just repr <- matchAddr (typeWidth val') -> SomeExt val' (Extension False repr)
    _ -> SomeExt val (Extension False (addrWidthRepr @(ArchAddrWidth arch) undefined))

-- | `extendDyn ext end bs` parses the bytestring using the extension
-- and endianness information, and returns the extended value.
extendDyn :: Extension w -> Endianness -> BS.ByteString -> Integer
extendDyn (Extension True Addr32) end bs  = toInteger (bsWord32 end bs)
extendDyn (Extension True Addr64) end bs  = toInteger (bsWord64 end bs)
extendDyn (Extension False Addr32) end bs = toSigned n32 (toInteger (bsWord32 end bs))
extendDyn (Extension False Addr64) end bs = toSigned n64 (toInteger (bsWord64 end bs))

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

-- This function resolves jump table entries.
-- It is a recursive function that has an index into the jump table.
-- If the current index can be interpreted as a intra-procedural jump,
-- then it will add that to the current procedure.
-- This returns the last address read.
resolveAsAddr :: forall w
              .  Memory w
              -> Endianness
              -> [MemChunk w]
              -> Maybe (MemAddr w)
resolveAsAddr mem endianness l = addrWidthClass (memAddrWidth mem) $
  case l of
    [ByteRegion bs] ->
      case addrRead endianness bs of
        Just a -> pure $! absoluteAddr a
        Nothing -> error $ "internal: resolveAsAddr given short chunk list."
    [RelocationRegion r] -> do
        when (relocationIsRel r) $ Nothing
        case relocationSym r of
          SymbolRelocation{} -> Nothing
          SectionIdentifier idx -> do
            addr <- Map.lookup idx (memSectionIndexMap mem)
            pure $! segoffAddr addr & incAddr (toInteger (relocationOffset r))
          SegmentBaseAddr idx -> do
            seg <- Map.lookup idx (memSegmentIndexMap mem)
            pure $! segmentOffAddr seg (relocationOffset r)
          LoadBaseAddr -> do
            memBaseAddr mem
    _ -> Nothing

-- This function resolves jump table entries.
-- It is a recursive function that has an index into the jump table.
-- If the current index can be interpreted as a intra-procedural jump,
-- then it will add that to the current procedure.
-- This returns the last address read.
resolveRelativeJumps :: forall arch w
                        .  ( MemWidth (ArchAddrWidth arch)
                        , IPAlignment arch
                        , RegisterInfo (ArchReg arch)
                        )
                     => Memory (ArchAddrWidth arch)
                     -> ArchSegmentOff arch
           --          -> MemRepr (BVType w)
                     -> BoundedMemArray arch (BVType w)
                     -> Extension w
                     -> Maybe (V.Vector (ArchSegmentOff arch))
resolveRelativeJumps mem base arrayRead ext = do
  let slices = arSlices arrayRead
  BVMemRepr _sz endianness <- pure $ arEltType arrayRead
  forM slices $ \l -> do
    case l of
      [ByteRegion bs]
        | tgtAddr <- segoffAddr base
                     & incAddr (extendDyn ext endianness bs)
        , Just tgt <- asSegmentOff mem (toIPAligned @arch tgtAddr)
        , Perm.isExecutable (segmentFlags (segoffSegment tgt))
          -> Just tgt
      _ -> Nothing

type JumpTableClassifierContext arch ids =
    ( Memory (ArchAddrWidth arch)
    , AbsProcessorState (ArchReg arch) ids
    , Jmp.IntraJumpBounds arch ids
    , ArchAddrValue arch ids
    )

type JumpTableClassifierResult arch ids =
   (JumpTableLayout arch, V.Vector (ArchSegmentOff arch), ArchAddrValue arch ids)

type JumpTableClassifier arch ids s =
  ReaderT (JumpTableClassifierContext arch ids) Classifier (JumpTableClassifierResult arch ids)

matchAbsoluteJumpTable
  :: forall arch ids s
  .  ArchConstraints arch
  => JumpTableClassifier arch ids s
matchAbsoluteJumpTable = classifierName "Absolute jump table" $ do
  (mem, aps, jmpBounds, ip) <- ask
  (arrayRead, idx) <- lift $ matchBoundedMemArray mem aps jmpBounds ip
  unless (isReadOnlyBoundedMemArray arrayRead) $ do
    fail "Bounded mem array is not read only."
  endianness <-
    case arEltType arrayRead of
      BVMemRepr _arByteCount e -> pure e
  let go :: Int
         -> [MemChunk (ArchAddrWidth arch)]
         -> Classifier (MemSegmentOff (ArchAddrWidth arch))
      go entryIndex contents = do
        addr <- case resolveAsAddr mem endianness contents of
                  Just a -> pure a
                  Nothing -> fail "Could not resolve jump table contents as absolute address."
        tgt <- case asSegmentOff mem (toIPAligned @arch addr) of
                 Just t -> pure t
                 Nothing ->
                   fail $
                     "Could not resolve jump table entry " ++ show entryIndex
                     ++ " value " ++ show addr ++ " as segment offset.\n" ++ show mem
        unless (Perm.isExecutable (segmentFlags (segoffSegment tgt))) $
          fail $ "Jump table contents non-executable."
        pure tgt
  tbl <- lift $ V.zipWithM go (V.generate (V.length (arSlices arrayRead)) id) (arSlices arrayRead)
  pure (AbsoluteJumpTable arrayRead, tbl, idx)

matchRelativeJumpTable
  :: forall arch ids s
  .  ArchConstraints arch
  => JumpTableClassifier arch ids s
matchRelativeJumpTable = classifierName "Relative jump table" $ do
  (mem, aps, jmpBounds, ip) <- ask
  -- gcc-style PIC jump tables on x86 use, roughly,
  --     ip = jmptbl + jmptbl[index]
  -- where jmptbl is a pointer to the lookup table.
  Just unalignedIP <- pure $ fromIPAligned ip
  Just (tgtBase, tgtOffset) <- pure $ valueAsMemOffset mem aps unalignedIP
  SomeExt shortOffset ext <- pure $ matchExtension tgtOffset
  (arrayRead, idx) <- lift $ matchBoundedMemArray mem aps jmpBounds shortOffset
  unless (isReadOnlyBoundedMemArray arrayRead) $ do
    fail $ "Jump table memory array must be read only."
  Just tbl <- pure $ resolveRelativeJumps mem tgtBase arrayRead ext
  pure (RelativeJumpTable tgtBase arrayRead ext, tbl, idx)

------------------------------------------------------------------------
-- reecordWriteStmts

-- | Mark addresses written to memory that point to code as function
-- entry points.
recordWriteStmts :: ArchitectureInfo arch
                 -> Memory (ArchAddrWidth arch)
                 -> AbsProcessorState (ArchReg arch) ids
                 -> Jmp.IntraJumpBounds arch ids
                 -> [ArchSegmentOff arch]
                 -> [Stmt arch ids]
                 -> ( AbsProcessorState (ArchReg arch) ids
                    , Jmp.IntraJumpBounds arch ids
                    , [ArchSegmentOff arch]
                    )
recordWriteStmts _archInfo _mem absState jmpBounds writtenAddrs [] =
  seq absState $ seq jmpBounds $ (absState, jmpBounds, writtenAddrs)
recordWriteStmts ainfo mem absState jmpBounds writtenAddrs (stmt:stmts) =
  seq absState $ seq jmpBounds $ do
    let absState' = absEvalStmt ainfo absState stmt
    let jmpBounds' = withArchConstraints ainfo $ Jmp.execStatement jmpBounds stmt
    let writtenAddrs' =
          case stmt of
            WriteMem _addr repr v
              | Just Refl <- testEquality repr (addrMemRepr ainfo) ->
                withArchConstraints ainfo $
                  let addrs = identifyConcreteAddresses mem (transferValue absState v)
                   in filter isExecutableSegOff addrs ++ writtenAddrs
            _ ->
              writtenAddrs
    recordWriteStmts ainfo mem absState' jmpBounds' writtenAddrs' stmts

------------------------------------------------------------------------
-- ParseContext

-- | Information needed to parse the processor state
data ParseContext arch ids =
  ParseContext { pctxMemory         :: !(Memory (ArchAddrWidth arch))
               , pctxArchInfo       :: !(ArchitectureInfo arch)
               , pctxKnownFnEntries :: !(Set (ArchSegmentOff arch))
                 -- ^ Entry addresses for known functions (e.g. from
                 -- symbol information)
                 --
                 -- The discovery process will not create
                 -- intra-procedural jumps to the entry points of new
                 -- functions.
               , pctxFunAddr        :: !(ArchSegmentOff arch)
                 -- ^ Address of function containing this block.
               , pctxAddr           :: !(ArchSegmentOff arch)
                 -- ^ Address of the current block
               , pctxExtResolution :: [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                 -- ^ Externally-provided resolutions for classification
                 -- failures, which are used in parseFetchAndExecute
               }

-- | Get the memory representation associated with pointers in the
-- given architecture.
addrMemRepr :: ArchitectureInfo arch -> MemRepr (BVType (RegAddrWidth (ArchReg arch)))
addrMemRepr arch_info =
  case archAddrWidth arch_info of
    Addr32 -> BVMemRepr n4 (archEndianness arch_info)
    Addr64 -> BVMemRepr n8 (archEndianness arch_info)

identifyCallTargets :: forall arch ids
                    .  (RegisterInfo (ArchReg arch))
                    => Memory (ArchAddrWidth arch)
                    -> AbsProcessorState (ArchReg arch) ids
                       -- ^ Abstract processor state just before call.
                    -> RegState (ArchReg arch) (Value arch ids)
                    -> [ArchSegmentOff arch]
identifyCallTargets mem absState regs = do
  -- Code pointers from abstract domains.
  let def = identifyConcreteAddresses mem $ transferValue absState (regs^.boundValue ip_reg)
  case regs^.boundValue ip_reg of
    BVValue _ x ->
      maybeToList $ resolveAbsoluteAddr mem (fromInteger x)
    RelocatableValue _ a ->
      maybeToList $ asSegmentOff mem a
    SymbolValue{} -> []
    AssignedValue a ->
      case assignRhs a of
        -- See if we can get a value out of a concrete memory read.
        ReadMem addr (BVMemRepr _ end)
          | Just laddr <- valueAsMemAddr addr
          , Right val <- readSegmentOff mem end laddr ->
            val : def
        _ -> def
    Initial _ -> def

-- | @stripPLTRead assignId prev rest@ looks for a read of @assignId@
-- from the end of @prev@, and if it finds it returns the
-- concatenation of the instruction before the read in @prev@ and
-- @rest@.
--
-- The read may appear before comment and @instructionStart@
-- instructions, but otherwise must be at the end of the instructions
-- in @prev@.
stripPLTRead :: ArchConstraints arch
              => AssignId ids tp -- ^ Identifier of write to remove
              -> Seq (Stmt arch ids)
              -> Seq (Stmt arch ids)
              -> Maybe (Seq (Stmt arch ids))
stripPLTRead readId next rest =
  case Seq.viewr next of
    Seq.EmptyR -> Nothing
    prev Seq.:> lastStmt -> do
      let cont = stripPLTRead readId prev (lastStmt Seq.<| rest)
      case lastStmt of
        AssignStmt (Assignment stmtId rhs)
          | Just Refl <- testEquality readId stmtId -> Just (prev Seq.>< rest)
            -- Fail if the read to delete is used in later computations
          | Set.member (Some readId) (foldMapFC refsInValue rhs) ->
              Nothing
          | otherwise ->
            case rhs of
              EvalApp{} -> cont
              SetUndefined{} -> cont
              _ -> Nothing
        InstructionStart{} -> cont
        ArchState{} -> cont
        Comment{} -> cont
        _ -> Nothing

removeUnassignedRegs :: forall arch ids
                     .  RegisterInfo (ArchReg arch)
                     => RegState (ArchReg arch) (Value arch ids)
                        -- ^ Initial register values
                     -> RegState (ArchReg arch) (Value arch ids)
                        -- ^ Final register values
                     -> MapF.MapF (ArchReg arch) (Value arch ids)
removeUnassignedRegs initRegs finalRegs =
  let keepReg :: forall tp . ArchReg arch tp -> Value arch ids tp -> Bool
      keepReg r finalVal
         | Just Refl <- testEquality r ip_reg = False
         | Just Refl <- testEquality initVal finalVal = False
         | otherwise = True
        where initVal = initRegs^.boundValue r
   in MapF.filterWithKey keepReg (regStateMap finalRegs)

-- | Return true if any value in structure contains the given
-- identifier.
containsAssignId :: forall t arch ids itp
                 .  FoldableF t
                 => AssignId ids itp
                    -- ^ Forbidden assignment -- may not appear in terms.
                 -> t (Value arch ids)
                 -> Bool
containsAssignId droppedAssign =
  let hasId :: forall tp . Value arch ids tp -> Any
      hasId v = Any (Set.member (Some droppedAssign) (refsInValue v))
   in getAny . foldMapF hasId

-- | Stores the main block features that may changes from parsing a block.
data ParsedContents arch ids =
  ParsedContents { parsedNonterm :: !([Stmt arch ids])
                   -- ^ The non-terminal statements in the block
                 , parsedTerm  :: !(ParsedTermStmt arch ids)
                   -- ^ The terminal statement in the block.
                 , writtenCodeAddrs :: ![ArchSegmentOff arch]
                 -- ^ Addresses marked executable that were written to memory.
                 , intraJumpTargets :: ![IntraJumpTarget arch]
                 , newFunctionAddrs :: ![ArchSegmentOff arch]
                   -- ^ List of candidate functions found when parsing block.
                   --
                   -- Note. In a binary, these could denote the non-executable
                   -- segments, so they are filtered before traversing.
                 }

-- | @normBool b q@ returns a pair where for each `NotApp` applied to @b@, we recursively
-- take the argument to `NotApp` and the Boolean.
--
-- This is used to compare if one value is equal to or the syntactic
-- complement of another value.
normBool :: Value arch ids BoolType -> Bool -> (Value arch ids BoolType, Bool)
normBool x b
  | AssignedValue a <- x
  , EvalApp (NotApp xn) <- assignRhs a =
      normBool xn (not b)
  | otherwise = (x,b)

-- | This computes the abstract state for the start of a block for a
-- given branch target.  It is used so that we can make use of the
-- branch condition to simplify the abstract state.
branchBlockState :: forall a ids t
               .  ( Foldable t
                  )
               => ArchitectureInfo a
               -> AbsProcessorState (ArchReg a) ids
               -> t (Stmt a ids)
               -> RegState (ArchReg a) (Value a ids)
                  -- ^  Register values
               -> Value a ids BoolType
                  -- ^ Branch condition
               -> Bool
                  -- ^ Flag indicating if branch is true or false.
               -> AbsBlockState (ArchReg a)
branchBlockState ainfo ps0 stmts regs c0 isTrue0 =
  withArchConstraints ainfo $
    let (c,isTrue) = normBool c0 isTrue0
        ps = refineProcState c isTrue ps0
        mapReg :: ArchReg a tp -> Value a ids tp -> Value a ids tp
        mapReg _r v
          | AssignedValue a <- v
          , EvalApp (Mux _ cv0 tv fv) <- assignRhs a
          , (cv, b) <- normBool cv0 isTrue
          , cv == c =
              if b then tv else fv
          | otherwise =
              v
        refinedRegs = mapRegsWith mapReg regs
     in finalAbsBlockState (foldl' (absEvalStmt ainfo) ps stmts) refinedRegs

type ClassificationError = String

data Classifier o = ClassifyFailed    [ClassificationError]
                  | ClassifySucceeded [ClassificationError] o

classifierName :: String -> ReaderT i Classifier a -> ReaderT i Classifier a
classifierName nm (ReaderT m) = ReaderT $ \i ->
  case m i of
    ClassifyFailed [] -> ClassifyFailed [nm ++ " classification failed."]
    ClassifyFailed l  -> ClassifyFailed (fmap ((nm ++ ": ") ++)  l)
    ClassifySucceeded l a -> ClassifySucceeded (fmap ((nm ++ ": ") ++)  l) a

classifyFail :: Classifier a
classifyFail = ClassifyFailed []

classifySuccess :: a -> Classifier a
classifySuccess = \x -> ClassifySucceeded [] x

classifyBind :: Classifier a -> (a -> Classifier b) -> Classifier b
classifyBind m f =
  case m of
    ClassifyFailed e -> ClassifyFailed e
    ClassifySucceeded [] a -> f a
    ClassifySucceeded l a ->
      case f a of
        ClassifyFailed    e   -> ClassifyFailed    (l++e)
        ClassifySucceeded e b -> ClassifySucceeded (l++e) b

classifyAppend :: Classifier a -> Classifier a -> Classifier a
classifyAppend m n =
  case m of
    ClassifySucceeded e a -> ClassifySucceeded e a
    ClassifyFailed [] -> n
    ClassifyFailed e ->
      case n of
        ClassifySucceeded f a -> ClassifySucceeded (e++f) a
        ClassifyFailed f      -> ClassifyFailed    (e++f)

instance Alternative Classifier where
  empty = classifyFail
  (<|>) = classifyAppend

instance Functor Classifier where
  fmap = liftA

instance Applicative Classifier where
  pure = classifySuccess
  (<*>) = ap

instance Monad Classifier where
  (>>=) = classifyBind
#if !(MIN_VERSION_base(4,13,0))
  fail = Fail.fail
#endif

instance Fail.MonadFail Classifier where
  fail = \m -> ClassifyFailed [m]


{-| The fields of the 'BlockClassifierContext' are:

  [@ParseContext ...@]: The context for the parse

  [@RegState ...@]: Initial register values

  [@Seq (Stmt ...)@]: The statements in the block

  [@AbsProcessorState ...@]: Abstract state of registers prior to
                             terminator statement being executed.

  [@Jmp.IntraJumpBounds ...@]: Bounds prior to terminator statement
                               being executed.

  [@ArchSegmentOff arch@]: Address of all segments written to memory

  [@RegState ...@]: Final register values
-}
data BlockClassifierContext arch ids = BlockClassifierContext
  { classifierParseContext  :: ParseContext arch ids
  -- ^ Information needed to construct abstract processor states
  , classifierInitRegState  :: RegState (ArchReg arch) (Value arch ids)
  -- ^ The (concrete) register state at the beginning of the block
  , classifierStmts         :: Seq (Stmt arch ids)
  -- ^ The statements of the block (without the terminator)
  , classifierAbsState      :: AbsProcessorState (ArchReg arch) ids
  -- ^ The abstract processor state before the terminator is executed
  , classifierJumpBounds    :: Jmp.IntraJumpBounds arch ids
  -- ^ The relational abstract processor state before the terminator is executed
  , classifierWrittenAddrs  :: [ArchSegmentOff arch]
  -- ^ The addresses of observed memory writes in the block
  , classifierFinalRegState :: RegState (ArchReg arch) (Value arch ids)
  -- ^ The final (concrete) register state before the terminator is executed
  }

type BlockClassifier arch ids =
  ReaderT (BlockClassifierContext arch ids)
          Classifier
          (ParsedContents arch ids)

classifyDirectJump :: RegisterInfo (ArchReg arch)
                   => ParseContext arch ids
                   -> String
                   -> Value arch ids (BVType (ArchAddrWidth arch))
                   -> ReaderT i Classifier (MemSegmentOff (ArchAddrWidth arch))
classifyDirectJump ctx nm v = do
  ma <- case valueAsMemAddr v of
          Nothing ->  fail $ nm ++ " value " ++ show v ++ " is not a valid address."
          Just a -> pure a
  a <- case asSegmentOff (pctxMemory ctx) ma of
         Nothing ->
           fail $ nm ++ " value " ++ show v ++ " is not a segment offset in " ++ show (pctxMemory ctx) ++ "."
         Just sa -> pure sa
  when (not (segmentFlags (segoffSegment a) `Perm.hasPerm` Perm.execute)) $ do
    fail $ nm ++ " value " ++ show a ++ " is not executable."
  when (a == pctxFunAddr ctx) $ do
    fail $ nm ++ " value " ++ show a ++ " refers to function start."
  when (a `Set.member` pctxKnownFnEntries ctx) $ do
    fail $ nm ++ " value " ++ show a ++ " is a known function entry."
  pure a

branchClassifier :: BlockClassifier arch ids
branchClassifier = classifierName "Branch" $ do
  bcc <- ask
  let ctx = classifierParseContext bcc
  let finalRegs = classifierFinalRegState bcc
  let writtenAddrs = classifierWrittenAddrs bcc
  let absState = classifierAbsState bcc
  let jmpBounds = classifierJumpBounds bcc
  let stmts = classifierStmts bcc
  let ainfo = pctxArchInfo ctx
  withArchConstraints ainfo $ do
    -- The block ends with a Mux, so we turn this into a `ParsedBranch` statement.
    let ipVal = finalRegs^.boundValue ip_reg
    (c,t,f) <- case valueAsApp ipVal of
                 Just (Mux _ c t f) -> pure (c,t,f)

                 _ -> fail $ "IP is not an mux:\n"
                          ++ show (ppValueAssignments ipVal)
    trueTgtAddr  <- classifyDirectJump ctx "True branch"  t
    falseTgtAddr <- classifyDirectJump ctx "False branch" f

    let trueRegs  = finalRegs & boundValue ip_reg .~ t
    let falseRegs = finalRegs & boundValue ip_reg .~ f

    let trueAbsState  = branchBlockState ainfo absState stmts trueRegs c True
    let falseAbsState = branchBlockState ainfo absState stmts falseRegs c False
    let tJmp = Jmp.postBranchBounds jmpBounds c True  trueRegs
        fJmp = Jmp.postBranchBounds jmpBounds c False falseRegs
    case (tJmp, fJmp) of
      (Right trueJmpState, Right falseJmpState) -> do
        pure $ ParsedContents { parsedNonterm = toList stmts
                              , parsedTerm  =
                                  ParsedBranch finalRegs c trueTgtAddr falseTgtAddr
                              , writtenCodeAddrs = writtenAddrs
                              , intraJumpTargets =
                                  [ (trueTgtAddr,  trueAbsState,  trueJmpState)
                                  , (falseTgtAddr, falseAbsState, falseJmpState)
                                  ]
                              , newFunctionAddrs = []
                              }
      -- The false branch is impossible.
      (Right trueJmpState, Left _) -> do
        pure $ ParsedContents { parsedNonterm = toList stmts
                              , parsedTerm  = ParsedJump finalRegs trueTgtAddr
                              , writtenCodeAddrs = writtenAddrs
                              , intraJumpTargets =
                                  [(trueTgtAddr, trueAbsState, trueJmpState)]
                              , newFunctionAddrs = []
                              }
      -- The true branch is impossible.
      (Left _ , Right falseJmpState) -> do
        pure $ ParsedContents { parsedNonterm = toList stmts
                              , parsedTerm  = ParsedJump finalRegs falseTgtAddr
                              , writtenCodeAddrs = writtenAddrs
                              , intraJumpTargets =
                                  [(falseTgtAddr, falseAbsState, falseJmpState)]
                              , newFunctionAddrs = []
                              }
      -- Both branches were deemed impossible
      (Left _ , Left _) -> do
        fail $ "Branch targets are both unreachable."

-- |  Use architecture-specific callback to check if last statement was a call.
--
-- Note that in some cases the call is known not to return, and thus
-- this code will never jump to the return value.
callClassifier :: BlockClassifier arch ids
callClassifier = do
  bcc <- ask
  let ctx = classifierParseContext bcc
  let finalRegs = classifierFinalRegState bcc
  let ainfo = pctxArchInfo ctx
  let mem = pctxMemory ctx
  Just (_prev_stmts, ret) <- pure $ identifyCall ainfo mem (classifierStmts bcc) finalRegs
  withArchConstraints ainfo $ do
    pure $ ParsedContents { parsedNonterm = toList (classifierStmts bcc)
                          , parsedTerm  = ParsedCall finalRegs (Just ret)
                            -- The return address may be written to
                            -- stack, but is highly unlikely to be
                            -- a function entry point.
                          , writtenCodeAddrs = filter (\a -> a /= ret) (classifierWrittenAddrs bcc)
                            --Include return target
                          , intraJumpTargets =
                              [( ret
                               , postCallAbsState ainfo (classifierAbsState bcc) finalRegs ret
                               , Jmp.postCallBounds (archCallParams ainfo) (classifierJumpBounds bcc) finalRegs
                               )]
                            -- Use the abstract domain to look for new code pointers for the current IP.
                          , newFunctionAddrs = identifyCallTargets mem (classifierAbsState bcc) finalRegs
                          }

-- | Check this block ends with a return as identified by the
-- architecture-specific processing.  Basic return identification
-- can be performed by detecting when the Instruction Pointer
-- (ip_reg) contains the 'ReturnAddr' symbolic value (initially
-- placed on the top of the stack or in the Link Register by the
-- architecture-specific state iniitializer).  However, some
-- architectures perform expression evaluations on this value before
-- loading the IP (e.g. ARM will clear the low bit in T32 mode or
-- the low 2 bits in A32 mode), so the actual detection process is
-- deferred to architecture-specific functionality.
returnClassifier :: BlockClassifier arch ids
returnClassifier = classifierName "Return" $ do
  bcc <- ask
  let ainfo = pctxArchInfo (classifierParseContext bcc)
  withArchConstraints ainfo $ do
    Just prev_stmts <- pure $ identifyReturn ainfo (classifierStmts bcc) (classifierFinalRegState bcc) (classifierAbsState bcc)
    pure $ ParsedContents { parsedNonterm = toList prev_stmts
                          , parsedTerm = ParsedReturn (classifierFinalRegState bcc)
                          , writtenCodeAddrs = classifierWrittenAddrs bcc
                          , intraJumpTargets = []
                          , newFunctionAddrs = []
                          }

-- | Jumps concrete addresses are intra-procedural if the call
-- identification fails.
directJumpClassifier :: BlockClassifier arch ids
directJumpClassifier = classifierName "Jump" $ do
  bcc <- ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx
  withArchConstraints ainfo $ do

    tgt_mseg <- classifyDirectJump ctx "Jump" (classifierFinalRegState bcc ^. boundValue ip_reg)

    let abst = finalAbsBlockState (classifierAbsState bcc) (classifierFinalRegState bcc)
    let abst' = abst & setAbsIP tgt_mseg
    let tgtBnds = Jmp.postJumpBounds (classifierJumpBounds bcc) (classifierFinalRegState bcc)
    pure $ ParsedContents { parsedNonterm = toList (classifierStmts bcc)
                          , parsedTerm  = ParsedJump (classifierFinalRegState bcc) tgt_mseg
                          , writtenCodeAddrs = classifierWrittenAddrs bcc
                          , intraJumpTargets = [(tgt_mseg, abst', tgtBnds)]
                          , newFunctionAddrs = []
                          }

jumpTableClassifier :: forall arch ids . BlockClassifier arch ids
jumpTableClassifier = classifierName "Jump table" $ do
  bcc <- ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx
  let mem = pctxMemory ctx
  withArchConstraints ainfo $ do
    let jumpTableClassifiers
          =   matchAbsoluteJumpTable
          <|> matchRelativeJumpTable
    (_jt, entries, jumpIndex) <- lift $
      runReaderT jumpTableClassifiers (mem, classifierAbsState bcc, classifierJumpBounds bcc, classifierFinalRegState bcc^.curIP)

    let abst :: AbsBlockState (ArchReg arch)
        abst = finalAbsBlockState (classifierAbsState bcc) (classifierFinalRegState bcc)
    let nextBnds = Jmp.postJumpBounds (classifierJumpBounds bcc) (classifierFinalRegState bcc)
    let term = ParsedLookupTable (classifierFinalRegState bcc) jumpIndex entries
    pure $ seq abst $
      ParsedContents { parsedNonterm = toList (classifierStmts bcc)
                     , parsedTerm = term
                     , writtenCodeAddrs = classifierWrittenAddrs bcc
                     , intraJumpTargets =
                         [ (tgtAddr, abst & setAbsIP tgtAddr, nextBnds)
                         | tgtAddr <- V.toList entries
                         ]
                     , newFunctionAddrs = []
                     }

-- | Attempt to recognize PLT stub
pltStubClassifier :: BlockClassifier arch ids
pltStubClassifier = classifierName "PLT stub" $ do
  bcc <- ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx
  let mem = pctxMemory ctx
  withArchConstraints ainfo $ do

    -- The IP should jump to an address in the .got, so try to compute that.
    AssignedValue (Assignment valId v) <- pure $ classifierFinalRegState bcc ^. boundValue ip_reg
    ReadMem gotVal _repr <- pure $ v
    Just gotSegOff <- pure $ valueAsSegmentOff mem gotVal
    -- The .got contents should point to a relocation to the function
    -- that we will jump to.
    Right chunks <- pure $ segoffContentsAfter gotSegOff
    RelocationRegion r:_ <- pure $ chunks
    -- Check the relocation satisfies all the constraints we expect on PLT strub
    SymbolRelocation sym symVer <- pure $ relocationSym r
    unless (relocationOffset r == 0) $ fail "PLT stub requires 0 offset."
    when (relocationIsRel r) $ fail "PLT stub requires absolute relocation."
    when (toInteger (relocationSize r) /= toInteger (addrWidthReprByteCount (archAddrWidth ainfo))) $ do
      fail $ "PLT stub relocations must match address size."
    when (relocationIsSigned r) $ do
      fail $ "PLT stub relocations must be signed."
    when (relocationEndianness r /= archEndianness ainfo) $ do
      fail $ "PLT relocation endianness must match architecture."
    unless (relocationJumpSlot r) $ do
      fail $ "PLT relocations must be jump slots."
    -- The PLTStub terminator will implicitly read the GOT address, so we remove
    -- it from the list of statements.
    Just strippedStmts <- pure $ stripPLTRead valId (classifierStmts bcc) Seq.empty
    let strippedRegs = removeUnassignedRegs (classifierInitRegState bcc) (classifierFinalRegState bcc)
    when (containsAssignId valId strippedRegs) $ do
      fail $ "PLT IP must be assigned."
    pure $ ParsedContents { parsedNonterm = toList strippedStmts
                          , parsedTerm  = PLTStub strippedRegs gotSegOff (VerSym sym symVer)
                          , writtenCodeAddrs = classifierWrittenAddrs bcc
                          , intraJumpTargets = []
                          , newFunctionAddrs = []
                          }

-- | Attempt to recognize tail call.
tailCallClassifier :: BlockClassifier arch ids
tailCallClassifier = classifierName "Tail call" $ do
  bcc <- ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx
  let mem   = pctxMemory ctx
  -- Check for tail call when the calling convention seems to be satisfied.
  withArchConstraints ainfo $ do

    let spVal = classifierFinalRegState bcc ^. boundValue sp_reg
    -- Check to see if the stack pointer points to an offset of the initial stack.
    o <-
      case transferValue (classifierAbsState bcc) spVal of
        StackOffsetAbsVal _ o -> pure o
        _ -> fail $ "Not a stack offset"
    -- Stack stack is back to height when function was called.
    unless (o == 0) $
      fail "Expected stack height of 0"
    -- Return address is pushed
    unless (checkForReturnAddr ainfo (classifierFinalRegState bcc) (classifierAbsState bcc)) empty
    pure $ ParsedContents { parsedNonterm = toList (classifierStmts bcc)
                          , parsedTerm  = ParsedCall (classifierFinalRegState bcc) Nothing
                          , writtenCodeAddrs = classifierWrittenAddrs bcc
                          , intraJumpTargets = []
                          , newFunctionAddrs = identifyCallTargets mem (classifierAbsState bcc) (classifierFinalRegState bcc)
                          }

useExternalTargets :: ( OrdF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => BlockClassifierContext arch ids
                   -> Maybe [IntraJumpTarget arch]
useExternalTargets bcc = do
  let ctx = classifierParseContext bcc
  let finalRegs = classifierFinalRegState bcc
  let jmpBounds = classifierJumpBounds bcc
  let absState = classifierAbsState bcc
  let initRegs = classifierInitRegState bcc
  let ipVal = initRegs ^. boundValue ip_reg
  ipAddr <- valueAsSegmentOff (pctxMemory ctx) ipVal
  targets <- lookup ipAddr (pctxExtResolution ctx)
  let blockState = finalAbsBlockState absState finalRegs
  let nextInitJmpBounds = Jmp.postJumpBounds jmpBounds finalRegs
  return [ (tgt, blockState, nextInitJmpBounds) | tgt <- targets ]

-- | This parses a block that ended with a fetch and execute instruction.
parseFetchAndExecute :: forall arch ids
                     .  (RegisterInfo (ArchReg arch))
                     => ParseContext arch ids
                     -> RegState (ArchReg arch) (Value arch ids)
                        -- ^ Initial register values
                     -> [Stmt arch ids]
                        -- ^ Statements
                     -> RegState (ArchReg arch) (Value arch ids)
                        -- ^ Final register values
                     -> AbsProcessorState (ArchReg arch) ids
                     -> Jmp.IntraJumpBounds arch ids
                     -> [ArchSegmentOff arch]
                     -> ParsedContents arch ids
parseFetchAndExecute ctx initRegs stmts finalRegs absState jmpBounds writtenAddrs = do
  -- Try to figure out what control flow statement we have.
  let classCtx = BlockClassifierContext
        { classifierParseContext = ctx
        , classifierInitRegState = initRegs
        , classifierStmts = Seq.fromList stmts
        , classifierAbsState = absState
        , classifierJumpBounds = jmpBounds
        , classifierWrittenAddrs = writtenAddrs
        , classifierFinalRegState = finalRegs
        }
  let cl = branchClassifier
        <|> callClassifier
        <|> returnClassifier
        <|> directJumpClassifier
        <|> jumpTableClassifier
        <|> pltStubClassifier
        <|> tailCallClassifier
  case runReaderT cl classCtx of
    ClassifySucceeded _ m -> m
    ClassifyFailed rsns ->
      ParsedContents { parsedNonterm = stmts
                     , parsedTerm  = ClassifyFailure finalRegs rsns
                     , writtenCodeAddrs = writtenAddrs
                     , intraJumpTargets = fromMaybe [] (useExternalTargets classCtx)
                     , newFunctionAddrs = []
                     }

-- | this evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
parseBlock :: ParseContext arch ids
              -- ^ Context for parsing blocks.
           -> RegState (ArchReg arch) (Value arch ids)
           -- ^ Initial register values
           -> Block arch ids
              -- ^ Block to parse
           -> AbsBlockState (ArchReg arch)
              -- ^ Abstract state at start of block
           -> Jmp.InitJumpBounds arch
           -> ParsedContents arch ids
parseBlock ctx initRegs b absBlockState blockBnds = do
  let ainfo = pctxArchInfo ctx
  let mem   = pctxMemory ctx
  withArchConstraints (pctxArchInfo ctx) $ do
   let (absState, jmpBounds, writtenAddrs) =
         let initAbsState = initAbsProcessorState mem absBlockState
             initJmpBounds = Jmp.mkIntraJumpBounds blockBnds
          in recordWriteStmts ainfo mem initAbsState initJmpBounds [] (blockStmts b)
   case blockTerm b of
    FetchAndExecute finalRegs ->
      parseFetchAndExecute ctx initRegs (blockStmts b) finalRegs absState jmpBounds writtenAddrs

    -- Do nothing when this block ends in a translation error.
    TranslateError _ msg ->
      ParsedContents { parsedNonterm = blockStmts b
                     , parsedTerm = ParsedTranslateError msg
                     , writtenCodeAddrs = writtenAddrs
                     , intraJumpTargets = []
                     , newFunctionAddrs = []
                     }
    ArchTermStmt tstmt regs ->
      let r = postArchTermStmtAbsState ainfo mem absState jmpBounds regs tstmt
       in ParsedContents { parsedNonterm = blockStmts b
                         , parsedTerm  = ParsedArchTermStmt tstmt regs ((\(a,_,_) -> a) <$> r)
                         , writtenCodeAddrs = writtenAddrs
                         , intraJumpTargets = maybeToList r
                         , newFunctionAddrs = []
                         }

-- | This evaluates the statements in a block to expand the
-- information known about control flow targets of this block.
addBlock :: ArchConstraints arch
         => ArchSegmentOff arch
            -- ^ Address of the block to add.
         -> FoundAddr arch
            -- ^ State leading to explore block
         -> ArchBlockPrecond arch
            -- ^ State information needed to disassemble block at this address.
         -> FunM arch s ids ()
addBlock src finfo pr = do
  s <- use curFunCtx
  let ainfo = archInfo s
  let initRegs = initialBlockRegs ainfo src pr
  let mem = memory s

  nonceGen <- gets funNonceGen
  prev_block_map <- use $ curFunBlocks
  let maxSize :: Int
      maxSize =
        case Map.lookupGT src prev_block_map of
          Just (next,_) | Just o <- diffSegmentOff next src -> fromInteger o
          _ -> fromInteger (segoffBytesLeft src)
  (b0, sz) <- liftST $ disassembleFn ainfo nonceGen src initRegs maxSize
  -- Rewrite returned blocks to simplify expressions
#ifdef USE_REWRITER
  (_,b) <- do
    let archStmt = rewriteArchStmt ainfo
    let secAddrMap = memSectionIndexMap mem
    let rw = \_ -> pure
    termStmt <- pure rw <*> pure src
    liftST $ do
      ctx <- mkRewriteContext nonceGen (rewriteArchFn ainfo) archStmt termStmt secAddrMap
      rewriteBlock ainfo ctx b0
#else
  b <- pure b0
#endif

  extRes <- gets classifyFailureResolutions
  funAddr <- gets curFunAddr

  let ctx = ParseContext { pctxMemory         = memory s
                         , pctxArchInfo       = archInfo s
                         , pctxKnownFnEntries = s^.trustedFunctionEntryPoints
                         , pctxFunAddr        = funAddr
                         , pctxAddr           = src
                         , pctxExtResolution  = extRes
                         }
  let pc = parseBlock ctx initRegs b (foundAbstractState finfo) (foundJumpBounds finfo)
  let pb = ParsedBlock { pblockAddr    = src
                       , pblockPrecond = Right pr
                       , blockSize     = sz
                       , blockReason   = foundReason finfo
                       , blockAbstractState = foundAbstractState finfo
                       , blockJumpBounds = foundJumpBounds finfo
                       , pblockStmts     = parsedNonterm pc
                       , pblockTermStmt  = parsedTerm pc
                       }
  let pb' = dropUnusedCodeInParsedBlock (archInfo s) pb
  id %= addFunBlock src pb'
  curFunCtx %= markAddrsAsFunction (PossibleWriteEntry src) (writtenCodeAddrs pc)
            .  markAddrsAsFunction (CallTarget src)         (newFunctionAddrs pc)
  mapM_ (mergeIntraJump src) (intraJumpTargets pc)

-- | Record an error block with no statements for the given address.
recordErrorBlock :: ArchSegmentOff arch -> FoundAddr arch -> String -> FunM arch s ids ()
recordErrorBlock addr finfo err = do
  let pb = ParsedBlock { pblockAddr = addr
                       , pblockPrecond = Left err
                       , blockSize = 0
                       , blockReason = foundReason finfo
                       , blockAbstractState = foundAbstractState finfo
                       , blockJumpBounds    = foundJumpBounds finfo
                       , pblockStmts = []
                       , pblockTermStmt = ParsedTranslateError (Text.pack err)
                       }
  id %= addFunBlock addr pb

transfer :: ArchSegmentOff arch -> FunM arch s ids ()
transfer addr = do
  s <- use curFunCtx
  let ainfo = archInfo s
  withArchConstraints ainfo $ do
    mfinfo <- use $ foundAddrs . at addr
    let finfo = fromMaybe (error $ "transfer called on unfound address " ++ show addr ++ ".") $
                  mfinfo
    -- Get maximum number of bytes to disassemble
    case extractBlockPrecond ainfo addr (foundAbstractState finfo) of
      Left msg -> do
        recordErrorBlock addr finfo msg
      Right pr -> do
        addBlock addr finfo pr

------------------------------------------------------------------------
-- Main loop

-- | Loop that repeatedly explore blocks until we have explored blocks
-- on the frontier.
analyzeBlocks :: (ArchSegmentOff arch -> ST s ())
                 -- ^ Logging function to call when analyzing a new block.
              -> FunState arch s ids
              -> ST s (FunState arch s ids)
analyzeBlocks logBlock st =
  case Set.minView (st^.frontier) of
    Nothing -> return st
    Just (addr, next_roots) -> do
      logBlock addr
      st' <- execStateT (unFunM (transfer addr)) (st & frontier .~ next_roots)
      analyzeBlocks logBlock st'

mkFunState :: NonceGenerator (ST s) ids
           -> DiscoveryState arch
           -> FunctionExploreReason (ArchAddrWidth arch)
              -- ^ Reason to provide for why we are analyzing this function
              --
              -- This can be used to figure out why we decided a
              -- given address identified a code location.
           -> ArchSegmentOff arch
           -> [(ArchSegmentOff arch, [ArchSegmentOff arch])]
           -> FunState arch s ids
mkFunState gen s rsn addr extraIntraTargets = do
  let faddr = FoundAddr { foundReason = FunctionEntryPoint
                        , foundAbstractState = mkInitialAbsState (archInfo s) (memory s) addr
                        , foundJumpBounds    = withArchConstraints (archInfo s) $ Jmp.functionStartBounds
                        }
   in FunState { funReason = rsn
               , funNonceGen = gen
               , curFunAddr  = addr
               , _curFunCtx  = s
               , _curFunBlocks = Map.empty
               , _foundAddrs = Map.singleton addr faddr
               , _reverseEdges = Map.empty
               , _frontier   = Set.fromList [ addr ]
               , classifyFailureResolutions = extraIntraTargets
               }

mkFunInfo :: FunState arch s ids -> DiscoveryFunInfo arch ids
mkFunInfo fs =
  let addr = curFunAddr fs
      s = fs^.curFunCtx
   in DiscoveryFunInfo { discoveredFunReason = funReason fs
                       , discoveredFunAddr = addr
                       , discoveredFunSymbol = Map.lookup addr (symbolNames s)
                       , _parsedBlocks = fs^.curFunBlocks
                       , discoveredClassifyFailureResolutions = classifyFailureResolutions fs
                       }

-- | This analyzes the function at a given address, possibly
-- discovering new candidates.
--
-- This returns the updated state and the discovered control flow
-- graph for this function.
analyzeFunction :: (ArchSegmentOff arch -> ST s ())
                 -- ^ Logging function to call when analyzing a new block.
                -> ArchSegmentOff arch
                   -- ^ The address to explore
                -> FunctionExploreReason (ArchAddrWidth arch)
                -- ^ Reason to provide for why we are analyzing this function
                --
                -- This can be used to figure out why we decided a
                -- given address identified a code location.
                -> DiscoveryState arch
                -- ^ The current binary information.
                -> ST s (DiscoveryState arch, Some (DiscoveryFunInfo arch))
analyzeFunction logFn addr rsn s =
  case Map.lookup addr (s^.funInfo) of
    Just finfo -> pure (s, finfo)
    Nothing -> runFunctionAnalysis logFn addr rsn s []


-- | Analyze addresses that we have marked as functions, but not yet analyzed to
-- identify basic blocks, and discover new function candidates until we have
-- analyzed all function entry points.
--
-- If an exploreFnPred function exists in the DiscoveryState, then do not
-- analyze unexploredFunctions at addresses that do not satisfy this predicate.
analyzeDiscoveredFunctions :: DiscoveryState arch -> DiscoveryState arch
analyzeDiscoveredFunctions info =
  case Map.lookupMin (exploreOK $ info^.unexploredFunctions) of
    Nothing -> info
    Just (addr, rsn) ->
      analyzeDiscoveredFunctions $! fst (runST ((analyzeFunction (\_ -> pure ()) addr rsn info)))
  where exploreOK unexploredFnMap
          -- filter unexplored functions using the predicate if present
          | Just xpFnPred <- info^.exploreFnPred
          = Map.filterWithKey (\addr _r -> xpFnPred addr) unexploredFnMap
          | otherwise = unexploredFnMap


-- | Extend the analysis of a previously analyzed function with new
-- information about the transfers for a block in that function.  The
-- assumption is that the block in question previously had an unknown
-- transfer state condition, and that the new transfer addresses were
-- discovered by other means (e.g. SMT analysis).  The block in
-- question's terminal statement will be replaced by an ITE (from IP
-- -> new addresses) and the new addresses will be added to the
-- frontier for additional discovery.
addDiscoveredFunctionBlockTargets :: DiscoveryState arch
                                  -> DiscoveryFunInfo arch ids
                                  -- ^ The function for which we have learned additional information
                                  -> [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                                  -> DiscoveryState arch
addDiscoveredFunctionBlockTargets initState origFunInfo resolvedTargets =
  let rsn = discoveredFunReason origFunInfo
      funAddr = discoveredFunAddr origFunInfo
  in fst $ runST (runFunctionAnalysis (\_ -> pure ())
                                      funAddr rsn initState
                                      resolvedTargets)

runFunctionAnalysis :: (ArchSegmentOff arch -> ST s ())
                    -- ^ Logging function to call when analyzing a new block.
                    -> ArchSegmentOff arch
                    -- ^ The address to explore
                    -> FunctionExploreReason (ArchAddrWidth arch)
                    -- ^ Reason to provide for why we are analyzing this function
                    --
                    -- This can be used to figure out why we decided a
                    -- given address identified a code location.
                    -> DiscoveryState arch
                    -- ^ The current binary information.
                    -> [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                    -- ^ Additional identified intraprocedural jump targets
                    --
                    -- The pairs are: (address of the block jumped from, jump targets)
                    -> ST s (DiscoveryState arch, Some (DiscoveryFunInfo arch))
runFunctionAnalysis logFn addr rsn s extraIntraTargets = do
  Some gen <- newSTNonceGenerator
  let fs0 = mkFunState gen s rsn addr extraIntraTargets
  fs <- analyzeBlocks logFn fs0
  let finfo = mkFunInfo fs
  let s' = (fs^.curFunCtx)
           & funInfo             %~ Map.insert addr (Some finfo)
           & unexploredFunctions %~ Map.delete addr
  seq finfo $ seq s $ pure (s', Some finfo)


-- | This returns true if the address is writable and value is executable.
isDataCodePointer :: MemSegmentOff w -> MemSegmentOff w -> Bool
isDataCodePointer a v
  =  segmentFlags (segoffSegment a) `Perm.hasPerm` Perm.write
  && segmentFlags (segoffSegment v) `Perm.hasPerm` Perm.execute

addMemCodePointer :: (ArchSegmentOff arch, ArchSegmentOff arch)
                  -> DiscoveryState arch
                  -> DiscoveryState arch
addMemCodePointer (src,val) = markAddrAsFunction (CodePointerInMem src) val

exploreMemPointers :: [(ArchSegmentOff arch, ArchSegmentOff arch)]
                   -- ^ List of addresses and value pairs to use for
                   -- considering possible addresses.
                   -> DiscoveryState arch
                   -> DiscoveryState arch
exploreMemPointers mem_words info =
  flip execState info $ do
    let mem_addrs
          = filter (\(a,v) -> isDataCodePointer a v)
          $ mem_words
    mapM_ (modify . addMemCodePointer) mem_addrs

-- | Expand an initial discovery state by exploring from a given set of function
-- entry points.
cfgFromAddrsAndState :: forall arch
                     .  DiscoveryState arch
                     -> [ArchSegmentOff arch]
                     -- ^ Initial function entry points.
                     -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
                     -- ^ Function entry points in memory to be explored
                     -- after exploring function entry points.
                     --
                     -- Each entry contains an address and the value stored in it.
                     -> DiscoveryState arch
cfgFromAddrsAndState initial_state init_addrs mem_words =
  initial_state
    & markAddrsAsFunction InitAddr init_addrs
    & analyzeDiscoveredFunctions
    & exploreMemPointers mem_words
    & analyzeDiscoveredFunctions

-- | Construct an empty discovery state and populate it by exploring from a
-- given set of function entry points
cfgFromAddrs ::
     forall arch
  .  ArchitectureInfo arch
     -- ^ Architecture-specific information needed for doing control-flow exploration.
  -> Memory (ArchAddrWidth arch)
     -- ^ Memory to use when decoding instructions.
  -> AddrSymMap (ArchAddrWidth arch)
     -- ^ Map from addresses to the associated symbol name.
  -> [ArchSegmentOff arch]
     -- ^ Initial function entry points.
     -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
     -- ^ Function entry points in memory to be explored
     -- after exploring function entry points.
     --
     -- Each entry contains an address and the value stored in it.
  -> DiscoveryState arch
cfgFromAddrs ainfo mem addrSymMap =
  cfgFromAddrsAndState (emptyDiscoveryState mem addrSymMap ainfo)

------------------------------------------------------------------------
-- Resolve functions with logging

resolveFuns :: (ArchSegmentOff arch -> FunctionExploreReason (ArchAddrWidth arch) -> ST s Bool)
               -- ^ Callback for discovered functions
               --
               -- Should return true if we should analyze the function and false otherwise.
            -> (ArchSegmentOff arch -> ArchSegmentOff arch -> ST s ())
               -- ^ Callback for logging blocks discovered within function
               -- Arguments include the address of function and address of block.
            -> DiscoveryState arch
            -> ST s (DiscoveryState arch)
resolveFuns analyzeFun analyzeBlock info = seq info $
  case Map.minViewWithKey (info^.unexploredFunctions) of
    Nothing -> pure info
    Just ((addr, rsn), rest) -> do
      p <- analyzeFun addr rsn
      if p then do
        (info',_) <- analyzeFunction (analyzeBlock addr) addr rsn info
        resolveFuns analyzeFun analyzeBlock info'
       else
        resolveFuns analyzeFun analyzeBlock (info & unexploredFunctions .~ rest)

------------------------------------------------------------------------
-- Top-level discovery

-- | Options controlling 'completeDiscoveryState'.
data DiscoveryOptions
   = DiscoveryOptions { exploreFunctionSymbols :: !Bool
                        -- ^ If @True@, 'completeDiscoveryState'
                        -- should automatically explore all addresses
                        -- in the address-to-symbol map.
                      , exploreCodeAddrInMem :: !Bool
                        -- ^ If @True@, 'completeDiscoveryState' will
                        -- explore all potential code addresses in
                        -- memory after exploring other potential
                        -- functions.
                        --
                        -- This is effectively a hack that sometimes
                        -- allows discovering functions.  If you need
                        -- it, let the author's of Macaw know so that
                        -- we can find a more principled way.
                      , logAtAnalyzeFunction  :: !Bool
                        -- ^ Print a message each time we apply
                        -- discovery analysis to a new function.
                      , logAtAnalyzeBlock     :: !Bool
                        -- ^ Print a message each time we analyze a
                        -- block within a function.
                      }

-- | Some default options
defaultDiscoveryOptions :: DiscoveryOptions
defaultDiscoveryOptions =
  DiscoveryOptions { exploreFunctionSymbols = True
                   , exploreCodeAddrInMem   = False
                   , logAtAnalyzeFunction   = True
                   , logAtAnalyzeBlock      = False
                   }

ppSymbol :: MemWidth w => MemSegmentOff w -> AddrSymMap w -> String
ppSymbol addr sym_map =
  case Map.lookup addr sym_map of
    Just fnName -> show addr ++ " (" ++ BSC.unpack fnName ++ ")"
    Nothing  -> show addr

-- | Event for logging function
data DiscoveryEvent w
   = AnalyzeFunction !(MemSegmentOff w)
   | AnalyzeBlock !(MemSegmentOff w)

{-# DEPRECATED discoveryLogFn "02/17/2018 Stop using this" #-}

-- | Print out discovery event using options and address to symbol map.
discoveryLogFn :: MemWidth w
               => DiscoveryOptions
               -> AddrSymMap w
               -> DiscoveryEvent w
               -> ST RealWorld ()
discoveryLogFn disOpt symMap (AnalyzeFunction addr) = ioToST $ do
  when (logAtAnalyzeFunction disOpt) $ do
    hPutStrLn stderr $ "Analyzing function: " ++ ppSymbol addr symMap
    hFlush stderr
discoveryLogFn disOpt _ (AnalyzeBlock addr) = ioToST $ do
  when (logAtAnalyzeBlock disOpt) $ do
    hPutStrLn stderr $ "  Analyzing block: " ++ show addr

    hFlush stderr


ppFunReason :: MemWidth w => FunctionExploreReason w -> String
ppFunReason rsn =
  case rsn of
    InitAddr -> ""
    UserRequest -> ""
    PossibleWriteEntry a -> " (written at " ++ show a ++ ")"
    CallTarget a -> " (called at " ++ show a ++ ")"
    CodePointerInMem a -> " (in initial memory at " ++ show a ++ ")"

-- | Explore until we have found all functions we can.
--
-- This function is intended to make it easy to explore functions, and
-- can be controlled via 'DiscoveryOptions'.
completeDiscoveryState :: forall arch
                       .  DiscoveryState arch
                       -> DiscoveryOptions
                          -- ^ Options controlling discovery
                       -> (ArchSegmentOff arch -> Bool)
                          -- ^ Predicate to check if we should explore a function
                          --
                          -- Return true to explore all functions.
                       -> IO (DiscoveryState arch)
completeDiscoveryState initState disOpt funPred = do
 let ainfo = archInfo initState
 let mem = memory initState
 let symMap = symbolNames initState
 stToIO $ withArchConstraints ainfo $ do
  -- Add symbol table entries to discovery state if requested
  let postSymState
        | exploreFunctionSymbols disOpt =
            initState & markAddrsAsFunction InitAddr (Map.keys symMap)
        | otherwise = initState
  let analyzeFn addr rsn = ioToST $ do
        let b = funPred addr
        when (b && logAtAnalyzeFunction disOpt) $ do
          hPutStrLn stderr $ "Analyzing function: " ++ ppSymbol addr symMap ++ ppFunReason rsn
          hFlush stderr
        pure $! b
  let analyzeBlock _ addr = ioToST $ do
        when (logAtAnalyzeBlock disOpt) $ do
          hPutStrLn stderr $ "  Analyzing block: " ++ show addr
          hFlush stderr
  -- Discover functions
  postPhase1Discovery <- resolveFuns analyzeFn analyzeBlock postSymState
  -- Discovery functions from memory
  if exploreCodeAddrInMem disOpt then do
    -- Execute hack of just searching for pointers in memory.
    let mem_contents = withArchConstraints ainfo $ memAsAddrPairs mem LittleEndian
    resolveFuns analyzeFn analyzeBlock $ postPhase1Discovery & exploreMemPointers mem_contents
   else
    return postPhase1Discovery
