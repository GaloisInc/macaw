{- |
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This provides information about code discovered in binaries.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Discovery
       ( -- * DiscoveryInfo
         State.DiscoveryState(..)
       , State.emptyDiscoveryState
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
       , State.parsedBlocks
         -- * Parsed block
       , State.ParsedBlock
       , State.pblockAddr
       , State.blockSize
       , State.blockReason
       , State.blockStatementList
       , State.StatementList(..)
       , State.ParsedTermStmt(..)
         -- * Simplification
       , eliminateDeadStmts
       ) where

import           Control.Applicative
import           Control.Lens
import           Control.Monad.ST
import           Control.Monad.State.Strict
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V
import           Data.Word
import           GHC.IO (ioToST, stToIO)
import           System.IO

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

-- | This uses an assertion about a given value being true or false to
-- refine the information in an abstract processor state.
refineProcStateBounds :: ( OrdF (ArchReg arch)
                         , HasRepr (ArchReg arch) TypeRepr
                         )
                      => Value arch ids BoolType
                      -> Bool
                      -> AbsProcessorState (ArchReg arch) ids
                      -> AbsProcessorState (ArchReg arch) ids
refineProcStateBounds v isTrue ps =
  case indexBounds (Jmp.assertPred v isTrue) ps of
    Left{}    -> ps
    Right ps' -> ps'

------------------------------------------------------------------------
-- Eliminate dead code in blocks

-- | Add any values needed to compute term statement to demand set.
addTermDemands :: TermStmt arch ids -> DemandComp arch ids ()
addTermDemands t = do
  case t of
    FetchAndExecute regs -> do
      traverseF_ addValueDemands regs
    Branch v _ _ -> do
      addValueDemands v
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
eliminateDeadStmts :: ArchitectureInfo arch -> [Block arch ids] -> [Block arch ids]
eliminateDeadStmts ainfo bs0 = elimDeadStmtsInBlock demandSet <$> bs0
  where demandSet =
          runDemandComp (archDemandContext ainfo) $ do
            traverse_ addBlockDemands bs0

------------------------------------------------------------------------
-- Eliminate dead code in blocks

-- | Add any assignments needed to evaluate statements with side
-- effects and terminal statement to demand set.
addStatementListDemands :: StatementList arch ids -> DemandComp arch ids ()
addStatementListDemands sl = do
  mapM_ addStmtDemands (stmtsNonterm sl)
  case stmtsTerm sl of
    ParsedCall regs _ -> do
      traverseF_ addValueDemands regs
    ParsedJump regs _ -> do
      traverseF_ addValueDemands regs
    ParsedLookupTable regs _idx _tbl  -> do
      traverseF_ addValueDemands regs
    ParsedReturn regs -> do
      traverseF_ addValueDemands regs
    ParsedIte b x y -> do
      addValueDemands b
      addStatementListDemands x
      addStatementListDemands y
    ParsedArchTermStmt _ regs _ -> do
      traverseF_ addValueDemands regs
    ParsedTranslateError _ -> do
      pure ()
    ClassifyFailure regs -> do
      traverseF_ addValueDemands regs

-- | Apply the given predicate to all statements in the list and only
-- include statements that pass.
--
-- Note. This may break the program if one is not careful.
filterStmtList :: (Stmt arch ids -> Bool)
               -> StatementList arch ids
               -> StatementList arch ids
filterStmtList stmtPred s = do
  let term' =
        case stmtsTerm s of
          ParsedIte b x y ->
            let x' = filterStmtList stmtPred x
                y' = filterStmtList stmtPred y
             in ParsedIte b x' y'
          term -> term
   in s { stmtsNonterm = filter stmtPred (stmtsNonterm s)
        , stmtsTerm = term'
        }

-- | Eliminate all dead statements in blocks
dropUnusedCodeInParsedBlock :: ArchitectureInfo arch
                          -> ParsedBlock arch ids
                          -> ParsedBlock arch ids
dropUnusedCodeInParsedBlock ainfo b =
    b { blockStatementList = filterStmtList stmtPred l }
  where l = blockStatementList b
        demandSet =
          runDemandComp (archDemandContext ainfo) $ do
            addStatementListDemands l
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
markAddrsAsFunction :: FunctionExploreReason (ArchAddrWidth arch)
                    -> [ArchSegmentOff arch]
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
                -> AbsBlockState (ArchReg arch)
                   -- ^ The state of the system after jumping to new block.
                -> ArchSegmentOff arch
                   -- ^ Address we are trying to reach.
                -> FunM arch s ids ()
mergeIntraJump src ab tgt = do
  info <- uses curFunCtx archInfo
  withArchConstraints info $ do
  when (not (absStackHasReturnAddr ab)) $ do
    debug DCFG ("WARNING: Missing return value in jump from " ++ show src ++ " to\n" ++ show ab) $
      pure ()
  let rsn = NextIP src
  -- Associate a new abstract state with the code region.
  foundMap <- use foundAddrs
  case Map.lookup tgt foundMap of
    -- We have seen this block before, so need to join and see if
    -- the results is changed.
    Just old_info -> do
      case joinD (foundAbstractState old_info) ab of
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
      let found_info = FoundAddr { foundReason = rsn
                                 , foundAbstractState = ab
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
  , arStride :: !Integer
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

-- | See if the value can be interpreted as a read of memory
matchBoundedMemArray
  :: (MemWidth (ArchAddrWidth arch), RegisterInfo (ArchReg arch))
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> BVValue arch ids w
  -> Maybe (BoundedMemArray arch (BVType w), ArchAddrValue arch ids)
matchBoundedMemArray mem aps val
  | Just (ReadMem addr tp) <- valueAsRhs val
  , Just (base, offset) <- valueAsMemOffset mem aps addr
  , Just (stride, ixVal) <- valueAsStaticMultiplication offset
    -- Check stride covers at least number of bytes read.
  , memReprBytes tp <= stride
    -- Resolve a static upper bound to array.
  , Right (Jmp.IntegerUpperBound bnd)
      <- Jmp.unsignedUpperBound (aps^.indexBounds) ixVal
  , cnt <- bnd+1
    -- Check array actually fits in memory.
  , cnt * toInteger stride <= segoffBytesLeft base
    -- Get memory contents after base
  , Right contents <- segoffContentsAfter base
    -- Break up contents into a list of slices each with size stide
  , Right (strideSlices,_) <- sliceMemContents (fromInteger stride) cnt contents
    -- Take the given number of bytes out of each slices
  , Right slices <- traverse (\s -> fst <$> splitMemChunks s (fromInteger (memReprBytes tp)))
                             (V.fromList strideSlices)
  = let r = BoundedMemArray
          { arBase     = base
          , arStride   = stride
          , arEltType  = tp
          , arSlices   = slices
          }
     in Just (r, ixVal)

  | otherwise = Nothing

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
resolveAsAbsoluteAddr :: forall w
                    .  Memory w
                    -> Endianness
                    -> [MemChunk w]
                    -> Maybe (MemAddr w)
resolveAsAbsoluteAddr mem endianness l = addrWidthClass (memAddrWidth mem) $
  case l of
    [ByteRegion bs] -> do
        absoluteAddr <$> addrRead endianness bs
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

-- | Resolve an ip to a jump table.
matchJumpTableRef :: forall arch ids
                  .  ( IPAlignment arch
                     , MemWidth (ArchAddrWidth arch)
                     , RegisterInfo (ArchReg arch)
                     )
                  => Memory (ArchAddrWidth arch)
                  -> AbsProcessorState (ArchReg arch) ids
                  -> ArchAddrValue arch ids -- ^ Value that's assigned to the IP.
                  -> Maybe (JumpTableLayout arch, V.Vector (ArchSegmentOff arch), ArchAddrValue arch ids)
matchJumpTableRef mem aps ip

    -- Turn a plain read address into base + offset.
  | Just (arrayRead,idx) <- matchBoundedMemArray mem aps ip
  , isReadOnlyBoundedMemArray arrayRead
  , BVMemRepr _arByteCount endianness <- arEltType arrayRead = do
      let go :: [MemChunk (ArchAddrWidth arch)] -> Maybe (MemSegmentOff (ArchAddrWidth arch))
          go contents = do
            addr <- resolveAsAbsoluteAddr mem endianness contents
            tgt <- asSegmentOff mem (toIPAligned @arch addr)
            unless (Perm.isExecutable (segmentFlags (segoffSegment tgt))) $ Nothing
            pure tgt
      tbl <- traverse go (arSlices arrayRead)
      pure (AbsoluteJumpTable arrayRead, tbl, idx)

  -- gcc-style PIC jump tables on x86 use, roughly,
  --     ip = jmptbl + jmptbl[index]
  -- where jmptbl is a pointer to the lookup table.
  | Just unalignedIP <- fromIPAligned ip
  , Just (tgtBase, tgtOffset) <- valueAsMemOffset mem aps unalignedIP
  , SomeExt shortOffset ext <- matchExtension tgtOffset
  , Just (arrayRead, idx) <- matchBoundedMemArray mem aps shortOffset
  , isReadOnlyBoundedMemArray arrayRead
  , Just tbl <- resolveRelativeJumps mem tgtBase arrayRead ext
  = Just (RelativeJumpTable tgtBase arrayRead ext, tbl, idx)

  | otherwise
  = Nothing

------------------------------------------------------------------------
-- ParseState

-- | This describes information learned when analyzing a block to look
-- for code pointers and classify exit.
data ParseState arch ids =
  ParseState { _writtenCodeAddrs :: ![ArchSegmentOff arch]
               -- ^ Addresses marked executable that were written to memory.
             , _intraJumpTargets ::
                 ![(ArchSegmentOff arch, AbsBlockState (ArchReg arch))]
             , _newFunctionAddrs :: ![ArchSegmentOff arch]
               -- ^ List of candidate functions found when parsing block.
               --
               -- Note. In a binary, these could denote the non-executable
               -- segments, so they are filtered before traversing.
             }

-- | Code addresses written to memory.
writtenCodeAddrs :: Simple Lens (ParseState arch ids) [ArchSegmentOff arch]
writtenCodeAddrs = lens _writtenCodeAddrs (\s v -> s { _writtenCodeAddrs = v })

-- | Intraprocedural jump targets.
intraJumpTargets :: Simple Lens (ParseState arch ids) [(ArchSegmentOff arch, AbsBlockState (ArchReg arch))]
intraJumpTargets = lens _intraJumpTargets (\s v -> s { _intraJumpTargets = v })

newFunctionAddrs :: Simple Lens (ParseState arch ids) [ArchSegmentOff arch]
newFunctionAddrs = lens _newFunctionAddrs (\s v -> s { _newFunctionAddrs = v })


-- | Mark addresses written to memory that point to code as function entry points.
recordWriteStmt :: ArchitectureInfo arch
                -> Memory (ArchAddrWidth arch)
                -> AbsProcessorState (ArchReg arch) ids
                -> Stmt arch ids
                -> State (ParseState arch ids) ()
recordWriteStmt arch_info mem regs stmt = do
  case stmt of
    WriteMem _addr repr v
      | Just Refl <- testEquality repr (addrMemRepr arch_info) -> do
          withArchConstraints arch_info $ do
          let addrs = identifyConcreteAddresses mem (transferValue regs v)
          writtenCodeAddrs %= (filter isExecutableSegOff addrs ++)
    _ -> return ()

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
                 -- The discovery process will not create intra-procedural
                 -- jumps to the entry points of new functions.
               , pctxFunAddr        :: !(ArchSegmentOff arch)
                 -- ^ Address of function this block is being parsed as
               , pctxAddr           :: !(ArchSegmentOff arch)
                 -- ^ Address of the current block
               , pctxBlockMap       :: !(Map Word64 (Block arch ids))
               }

addrMemRepr :: ArchitectureInfo arch -> MemRepr (BVType (RegAddrWidth (ArchReg arch)))
addrMemRepr arch_info =
  case archAddrWidth arch_info of
    Addr32 -> BVMemRepr n4 (archEndianness arch_info)
    Addr64 -> BVMemRepr n8 (archEndianness arch_info)

identifyCallTargets :: forall arch ids
                    .  (RegisterInfo (ArchReg arch))
                    => Memory (ArchAddrWidth arch)
                    -> AbsBlockState (ArchReg arch)
                       -- ^ Abstract processor state just before call.
                    -> RegState (ArchReg arch) (Value arch ids)
                    -> [ArchSegmentOff arch]
identifyCallTargets mem absState s = do
  -- Code pointers from abstract domains.
  let def = identifyConcreteAddresses mem (absState^.absRegState^.curIP)
  case s^.boundValue ip_reg of
    BVValue _ x ->
      maybeToList $ resolveAbsoluteAddr mem (fromInteger x)
    RelocatableValue _ a ->
      maybeToList $ asSegmentOff mem a
    SymbolValue{} -> def
    AssignedValue a ->
      case assignRhs a of
        -- See if we can get a value out of a concrete memory read.
        ReadMem addr (BVMemRepr _ end)
          | Just laddr <- valueAsMemAddr addr
          , Right val <- readSegmentOff mem end laddr ->
            val : def
        _ -> def
    Initial _ -> def

addNewFunctionAddrs :: [ArchSegmentOff arch]
                    -> State (ParseState arch ids) ()
addNewFunctionAddrs addrs =
  newFunctionAddrs %= (++addrs)

-- | This parses a block that ended with a fetch and execute instruction.
parseFetchAndExecute :: forall arch ids
                     .  ParseContext arch ids
                     -> Word64
                        -- ^ Index of this block
                     -> [Stmt arch ids]
                     -> AbsProcessorState (ArchReg arch) ids
                     -- ^ Registers prior to blocks being executed.
                     -> RegState (ArchReg arch) (Value arch ids)
                     -> State (ParseState arch ids) (StatementList arch ids, Word64)
parseFetchAndExecute ctx idx stmts regs s = do
  let mem = pctxMemory ctx
  let ainfo= pctxArchInfo ctx
  let absProcState' = absEvalStmts ainfo regs stmts
  withArchConstraints ainfo $ do
  -- See if next statement appears to end with a call.
  -- We define calls as statements that end with a write that
  -- stores the pc to an address.
  case () of
    _ | Just (Mux _ c t f) <- valueAsApp (s^.boundValue ip_reg) -> do
          mapM_ (recordWriteStmt ainfo mem absProcState') stmts

          let l_regs = refineProcStateBounds c True $
                          refineProcState c absTrue absProcState'
          let l_regs' = absEvalStmts ainfo l_regs stmts
          let lState = s & boundValue ip_reg .~ t
          (tStmts,trueIdx) <-
            parseFetchAndExecute ctx (idx+1) [] l_regs' lState

          let r_regs = refineProcStateBounds c False $
                         refineProcState c absFalse absProcState'
          let r_regs' = absEvalStmts ainfo r_regs stmts
          let rState = s & boundValue ip_reg .~ f

          (fStmts,falseIdx) <-
            parseFetchAndExecute ctx trueIdx [] r_regs' rState

          let ret = StatementList { stmtsIdent = idx
                                  , stmtsNonterm = stmts
                                  , stmtsTerm  = ParsedIte c tStmts fStmts
                                  , stmtsAbsState = absProcState'
                                  }
          pure (ret, falseIdx)

    -- The last statement was a call.
    -- Note that in some cases the call is known not to return, and thus
    -- this code will never jump to the return value.
    _ | Just (prev_stmts, ret) <- identifyCall ainfo mem stmts s  -> do
        mapM_ (recordWriteStmt ainfo mem absProcState') prev_stmts
        let abst = finalAbsBlockState absProcState' s
        seq abst $ do
        -- Merge caller return information
        intraJumpTargets %= ((ret, postCallAbsState ainfo abst ret):)
        -- Use the abstract domain to look for new code pointers for the current IP.
        addNewFunctionAddrs $
          identifyCallTargets mem abst s
        -- Use the call-specific code to look for new IPs.

        let r = StatementList { stmtsIdent = idx
                              , stmtsNonterm = toList prev_stmts
                              , stmtsTerm  = ParsedCall s (Just ret)
                              , stmtsAbsState = absProcState'
                              }
        pure (r, idx+1)

      -- This block ends with a return as identified by the
      -- architecture-specific processing.  Basic return
      -- identification can be performed by detecting when the
      -- Instruction Pointer (ip_reg) contains the 'ReturnAddr'
      -- symbolic value (initially placed on the top of the stack or
      -- in the Link Register by the architecture-specific state
      -- iniitializer).  However, some architectures perform
      -- expression evaluations on this value before loading the IP
      -- (e.g. ARM will clear the low bit in T32 mode or the low 2
      -- bits in A32 mode), so the actual detection process is
      -- deferred to architecture-specific functionality.
      | Just prev_stmts <- identifyReturn ainfo stmts s absProcState' -> do
        mapM_ (recordWriteStmt ainfo mem absProcState') prev_stmts

        let ret = StatementList { stmtsIdent = idx
                                , stmtsNonterm = toList prev_stmts
                                , stmtsTerm = ParsedReturn s
                                , stmtsAbsState = absProcState'
                                }
        pure (ret, idx+1)

      -- Jump to a block within this function.
      | Just tgt_mseg <- valueAsSegmentOff mem (s^.boundValue ip_reg)
        -- Check
      , segmentFlags (segoffSegment tgt_mseg) `Perm.hasPerm` Perm.execute

        -- Check the target address is not the entry point of this function.
        -- N.B. These should instead decompile into calls or tail calls.
      , tgt_mseg /= pctxFunAddr ctx

      -- If we are trusting known function entries, then only mark as an
      -- intra-procedural jump if the target is not a known function entry.
      , not (tgt_mseg `Set.member` pctxKnownFnEntries ctx) -> do

         mapM_ (recordWriteStmt ainfo mem absProcState') stmts
         -- Merge block state and add intra jump target.
         let abst = finalAbsBlockState absProcState' s
         let abst' = abst & setAbsIP tgt_mseg
         intraJumpTargets %= ((tgt_mseg, abst'):)
         let ret = StatementList { stmtsIdent = idx
                                 , stmtsNonterm = stmts
                                 , stmtsTerm  = ParsedJump s tgt_mseg
                                 , stmtsAbsState = absProcState'
                                 }
         pure (ret, idx+1)
      -- Block ends with what looks like a jump table.
      | Just (_jt, entries, jumpIndex) <- matchJumpTableRef mem absProcState' (s^.curIP) -> do

          mapM_ (recordWriteStmt ainfo mem absProcState') stmts

          let abst :: AbsBlockState (ArchReg arch)
              abst = finalAbsBlockState absProcState' s

          seq abst $ do

            forM_ entries $ \tgtAddr -> do
              let abst' = abst & setAbsIP tgtAddr
              intraJumpTargets %= ((tgtAddr, abst'):)

            let term = ParsedLookupTable s jumpIndex entries
            let ret = StatementList { stmtsIdent = idx
                                    , stmtsNonterm = stmts
                                    , stmtsTerm = term
                                    , stmtsAbsState = absProcState'
                                    }
            pure (ret,idx+1)

      -- Check for tail call when the stack pointer points to the return address.
      --
      -- TODO: this makes sense for x86, but is not correct for all architectures
      | ptrType    <- addrMemRepr ainfo
      , sp_val     <- s^.boundValue sp_reg
      , ReturnAddr <- absEvalReadMem absProcState' sp_val ptrType -> do
        finishWithTailCall absProcState'

      -- Is this a jump to a known function entry? We're already past the
      -- "identifyCall" case, so this must be a tail call, assuming we trust our
      -- known function entry info.
      | Just tgt_mseg <- valueAsSegmentOff mem (s^.boundValue ip_reg)
      , tgt_mseg `Set.member` pctxKnownFnEntries ctx -> do
        finishWithTailCall absProcState'

      -- Block that ends with some unknown
      | otherwise -> do
          mapM_ (recordWriteStmt ainfo mem absProcState') stmts
          let ret = StatementList { stmtsIdent = idx
                                  , stmtsNonterm = stmts
                                  , stmtsTerm  = ClassifyFailure s
                                  , stmtsAbsState = absProcState'
                                  }
          pure (ret,idx+1)

  where finishWithTailCall :: RegisterInfo (ArchReg arch)
                           => AbsProcessorState (ArchReg arch) ids
                           -> State (ParseState arch ids) (StatementList arch ids, Word64)
        finishWithTailCall absProcState' = do
          let mem = pctxMemory ctx
          mapM_ (recordWriteStmt (pctxArchInfo ctx) mem absProcState') stmts

          -- Compute final state
          let abst = finalAbsBlockState absProcState' s
          seq abst $ do

          -- Look for new instruction pointers
          addNewFunctionAddrs $
            identifyConcreteAddresses mem (abst^.absRegState^.curIP)

          let ret = StatementList { stmtsIdent = idx
                                  , stmtsNonterm = stmts
                                  , stmtsTerm  = ParsedCall s Nothing
                                  , stmtsAbsState = absProcState'
                                  }
          seq ret $ pure (ret,idx+1)

-- | this evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
parseBlock :: ParseContext arch ids
              -- ^ Context for parsing blocks.
           -> Word64
              -- ^ Index for next statements
           -> Block arch ids
              -- ^ Block to parse
           -> AbsProcessorState (ArchReg arch) ids
              -- ^ Abstract state at start of block
           -> State (ParseState arch ids) (StatementList arch ids, Word64)
parseBlock ctx idx b regs = do
  let mem       = pctxMemory ctx
  let ainfo = pctxArchInfo ctx
  withArchConstraints ainfo $ do
  case blockTerm b of
    Branch c lb rb -> do
      let blockMap = pctxBlockMap ctx
      -- FIXME: we should propagate c back to the initial block, not just b
      let absProcState' = absEvalStmts ainfo regs (blockStmts b)
      mapM_ (recordWriteStmt ainfo mem absProcState') (blockStmts b)

      let Just l = Map.lookup lb blockMap
      let l_regs = refineProcStateBounds c True $ refineProcState c absTrue absProcState'
      let Just r = Map.lookup rb blockMap
      let r_regs = refineProcStateBounds c False $ refineProcState c absFalse absProcState'

      let l_regs' = absEvalStmts ainfo l_regs (blockStmts b)
      let r_regs' = absEvalStmts ainfo r_regs (blockStmts b)

      (parsedTrueBlock,trueIdx)  <- parseBlock ctx (idx+1) l l_regs'
      (parsedFalseBlock,falseIdx) <- parseBlock ctx trueIdx r r_regs'

      let ret = StatementList { stmtsIdent = idx
                              , stmtsNonterm = blockStmts b
                              , stmtsTerm  = ParsedIte c parsedTrueBlock parsedFalseBlock
                              , stmtsAbsState = absProcState'
                              }
      pure (ret, falseIdx)

    FetchAndExecute s -> do
      parseFetchAndExecute ctx idx (blockStmts b) regs s

    -- Do nothing when this block ends in a translation error.
    TranslateError _ msg -> do
      -- FIXME: we should propagate c back to the initial block, not just b
      let absProcState' = absEvalStmts ainfo regs (blockStmts b)

      let ret = StatementList { stmtsIdent = idx
                              , stmtsNonterm = blockStmts b
                              , stmtsTerm = ParsedTranslateError msg
                              , stmtsAbsState = absProcState'
                              }
      pure (ret, idx+1)
    ArchTermStmt ts s -> do
      -- FIXME: we should propagate c back to the initial block, not just b
      let absProcState' = absEvalStmts ainfo regs (blockStmts b)
      mapM_ (recordWriteStmt ainfo mem absProcState') (blockStmts b)
      let abst = finalAbsBlockState absProcState' s
      -- Compute possible next IPS.
      let r = postArchTermStmtAbsState ainfo mem abst s ts
      case r of
        Just (addr,post) ->
          intraJumpTargets %= ((addr, post):)
        Nothing -> pure ()
      let ret = StatementList { stmtsIdent = idx
                              , stmtsNonterm = blockStmts b
                              , stmtsTerm  = ParsedArchTermStmt ts s (fst <$> r)
                              , stmtsAbsState = absProcState'
                              }
      pure (ret, idx+1)

-- | This evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
addBlocks :: ArchSegmentOff arch
                  -- ^ Address of theze blocks
               -> FoundAddr arch
                  -- ^ State leading to explore block
               -> Int
                  -- ^ Number of blocks covered
               -> Map Word64 (Block arch ids)
                  -- ^ Map from labelIndex to associated block
               -> FunM arch s ids ()
addBlocks src finfo sz blockMap =
  case Map.lookup 0 blockMap of
    Nothing -> do
      error $ "addBlocks given empty blockRegion."
    Just b -> do
      mem       <- uses curFunCtx memory
      let regs = initAbsProcessorState mem (foundAbstractState finfo)
      funAddr <- gets curFunAddr
      s <- use curFunCtx

      -- Combine entries of functions we've discovered thus far with
      -- undiscovered functions with entries marked InitAddr, which we assume is
      -- info we know from the symbol table or some other reliable source, and
      -- pass in. Only used in analysis if pctxTrustKnownFns is True.
      let knownFns =
            if s^.trustKnownFns then
              Set.union (Map.keysSet $ s^.funInfo)
                        (Map.keysSet $ Map.filter (== InitAddr) $ s^.unexploredFunctions)
             else
              Set.empty
      let ctx = ParseContext { pctxMemory         = memory s
                             , pctxArchInfo       = archInfo s
                             , pctxKnownFnEntries = knownFns
                             , pctxFunAddr        = funAddr
                             , pctxAddr           = src
                             , pctxBlockMap       = blockMap
                             }
      let ps0 = ParseState { _writtenCodeAddrs = []
                           , _intraJumpTargets = []
                           , _newFunctionAddrs = []
                           }
      let ((pblock,_), ps) = runState (parseBlock ctx 0 b regs) ps0
      let pb = ParsedBlock { pblockAddr = src
                           , blockSize = sz
                           , blockReason = foundReason finfo
                           , blockAbstractState = foundAbstractState finfo
                           , blockStatementList = pblock
                           }
      let pb' = dropUnusedCodeInParsedBlock (archInfo s) pb
      id %= addFunBlock src pb'
      curFunCtx %= markAddrsAsFunction (PossibleWriteEntry src) (ps^.writtenCodeAddrs)
                .  markAddrsAsFunction (CallTarget src)         (ps^.newFunctionAddrs)
      mapM_ (\(addr, abs_state) -> mergeIntraJump src abs_state addr) (ps^.intraJumpTargets)

transfer :: ArchSegmentOff arch -> FunM arch s ids ()
transfer addr = do
  s <- use curFunCtx
  let ainfo = archInfo s
  withArchConstraints ainfo $ do
  mfinfo <- use $ foundAddrs . at addr
  let finfo = fromMaybe (error $ "transfer called on unfound address " ++ show addr ++ ".") $
                mfinfo
  let mem = memory s
  nonceGen <- gets funNonceGen
  prev_block_map <- use $ curFunBlocks
  -- Get maximum number of bytes to disassemble
  let maxSize :: Int
      maxSize =
        case Map.lookupGT addr prev_block_map of
          Just (next,_) | Just o <- diffSegmentOff next addr -> fromInteger o
          _ -> fromInteger (segoffBytesLeft addr)
  let ab = foundAbstractState finfo
  (bs0, sz, maybeError) <- liftST $ disassembleFn ainfo nonceGen addr maxSize ab

#ifdef USE_REWRITER
  bs1 <- do
    let archStmt = rewriteArchStmt ainfo
    let secAddrMap = memSectionIndexMap mem
    liftST $ do
      ctx <- mkRewriteContext nonceGen (rewriteArchFn ainfo) archStmt secAddrMap
      traverse (rewriteBlock ainfo ctx) bs0
#else
  bs1 <- pure bs0
#endif

  -- If no blocks are returned, then we just add an empty parsed block.
  if null bs1 then do
    let errMsg = Text.pack $ fromMaybe "Unknown error" maybeError
    let stmts = StatementList
          { stmtsIdent = 0
          , stmtsNonterm = []
          , stmtsTerm = ParsedTranslateError errMsg
          , stmtsAbsState = initAbsProcessorState mem (foundAbstractState finfo)
          }
    let pb = ParsedBlock { pblockAddr = addr
                         , blockSize = sz
                         , blockReason = foundReason finfo
                         , blockAbstractState = foundAbstractState finfo
                         , blockStatementList = stmts
                         }
    id %= addFunBlock addr pb
   else do
    -- Rewrite returned blocks to simplify expressions

    -- Compute demand set
    let bs = bs1 -- eliminateDeadStmts ainfo bs1
    -- Call transfer blocks to calculate parsedblocks
    let blockMap = Map.fromList [ (blockLabel b, b) | b <- bs ]
    addBlocks addr finfo sz blockMap

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
           -> FunState arch s ids
mkFunState gen s rsn addr = do
  let faddr = FoundAddr { foundReason = FunctionEntryPoint
                        , foundAbstractState = mkInitialAbsState (archInfo s) (memory s) addr
                        }
   in FunState { funReason = rsn
               , funNonceGen = gen
               , curFunAddr  = addr
               , _curFunCtx  = s
               , _curFunBlocks = Map.empty
               , _foundAddrs = Map.singleton addr faddr
               , _reverseEdges = Map.empty
               , _frontier   = Set.singleton addr
               }

mkFunInfo :: FunState arch s ids -> DiscoveryFunInfo arch ids
mkFunInfo fs =
  let addr = curFunAddr fs
      s = fs^.curFunCtx
      nm = withArchConstraints (archInfo s) $
         fromMaybe (BSC.pack (show addr)) (Map.lookup addr (symbolNames s))
   in DiscoveryFunInfo { discoveredFunReason = funReason fs
                       , discoveredFunAddr = addr
                       , discoveredFunName = nm
                       , _parsedBlocks = fs^.curFunBlocks
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
    Nothing -> do
      Some gen <- newSTNonceGenerator
      let fs0 = mkFunState gen s rsn addr
      fs <- analyzeBlocks logFn fs0
      let finfo = mkFunInfo fs
      let s' = (fs^.curFunCtx)
             & funInfo             %~ Map.insert addr (Some finfo)
             & unexploredFunctions %~ Map.delete addr
      seq finfo $ seq s $ pure (s', Some finfo)

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
cfgFromAddrs ainfo mem symbols =
  cfgFromAddrsAndState (emptyDiscoveryState mem symbols ainfo)

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
