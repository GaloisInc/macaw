{- |
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This provides information about code discovered in binaries.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Macaw.Discovery
       ( -- * DiscoveryInfo
         State.DiscoveryState
       , State.emptyDiscoveryState
       , State.archInfo
       , State.memory
       , State.funInfo
       , State.exploredFunctions
       , State.symbolNames
       , State.ppDiscoveryStateBlocks
       , State.unexploredFunctions
       , Data.Macaw.Discovery.cfgFromAddrs
       , Data.Macaw.Discovery.cfgFromAddrsAndState
       , Data.Macaw.Discovery.markAddrsAsFunction
       , State.CodeAddrReason(..)
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

import           Control.Lens
import           Control.Monad.ST
import           Control.Monad.State.Strict
import qualified Data.ByteString.Char8 as BSC
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
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

import           Debug.Trace

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.AbsDomain.Refine
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
import           Data.Macaw.DebugLogging
import           Data.Macaw.Discovery.AbsEval
import           Data.Macaw.Discovery.State as State
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

#define USE_REWRITER 1

------------------------------------------------------------------------
-- Utilities

-- | Get code pointers out of a abstract value.
concretizeAbsCodePointers :: MemWidth w
                          => Memory w
                          -> AbsValue w (BVType w)
                          -> [MemSegmentOff w]
concretizeAbsCodePointers mem (FinSet s) =
  [ sa
  | a <- Set.toList s
  , sa <- maybeToList (resolveAbsoluteAddr mem (fromInteger a))
  , segmentFlags (msegSegment sa) `Perm.hasPerm` Perm.execute
  ]
concretizeAbsCodePointers _ (CodePointers s _) =
  [ sa
  | sa <- Set.toList s
  , segmentFlags (msegSegment sa) `Perm.hasPerm` Perm.execute
  ]
  -- FIXME: this is dangerous !!
concretizeAbsCodePointers _mem StridedInterval{} = [] -- FIXME: this case doesn't make sense
  -- debug DCFG ("I think these are code pointers!: " ++ show s) $ []
  -- filter (isCodeAddr mem) $ fromInteger <$> SI.toList s
concretizeAbsCodePointers _mem _ = []

{-
printAddrBacktrace :: Map (ArchMemAddr arch) (FoundAddr arch)
                   -> ArchMemAddr arch
                   -> CodeAddrReason (ArchAddrWidth arch)
                   -> [String]
printAddrBacktrace found_map addr rsn = do
  let pp msg = show addr ++ ": " ++ msg
  let prev prev_addr =
        case Map.lookup prev_addr found_map of
          Just found_info -> printAddrBacktrace found_map prev_addr (foundReason found_info)
          Nothing -> error $ "Unknown reason for address " ++ show prev_addr
  case rsn of
    InWrite src            -> pp ("Written to memory in block at address " ++ show src ++ ".") : prev src
    NextIP src             -> pp ("Target IP for " ++ show src ++ ".") : prev src
    CallTarget src         -> pp ("Target IP of call at " ++ show src ++ ".") : prev src
    InitAddr               -> [pp "Initial entry point."]
    CodePointerInMem src   -> [pp ("Memory address " ++ show src ++ " contained code.")]
    SplitAt src            -> pp ("Split from read of " ++ show src ++ ".") : prev src

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
-- Demanded subterm utilities

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
-- Memory utilities

-- | Return true if range is entirely contained within a single read only segment.Q
rangeInReadonlySegment :: MemWidth w
                       => MemSegmentOff w -- ^ Start of range
                       -> MemWord w -- ^ The size of the range
                       -> Bool
rangeInReadonlySegment mseg size =
     size <= segmentSize (msegSegment mseg) - msegOffset mseg
  && Perm.isReadonly (segmentFlags (msegSegment mseg))

------------------------------------------------------------------------
-- DiscoveryState utilities

-- | Mark a escaped code pointer as a function entry.
markAddrAsFunction :: CodeAddrReason (ArchAddrWidth arch)
                      -- ^ Information about why the code address was discovered
                      --
                      -- Used for debugging
                   -> ArchSegmentOff arch
                   -> DiscoveryState arch
                   -> DiscoveryState arch
markAddrAsFunction rsn addr s
  -- Skip if function is unexlored
  | Map.member addr (s^.funInfo) = s
  | otherwise = addrWidthClass (memAddrWidth (memory s)) $
    -- Only add function if the start is raw bytes.
    case contentsAfterSegmentOff addr of
      Right (ByteRegion _:_) ->
        s & unexploredFunctions %~ Map.insertWith (\_ old -> old) addr rsn
      _ -> s
-- | Mark a list of addresses as function entries with the same reason.
markAddrsAsFunction :: CodeAddrReason (ArchAddrWidth arch)
                    -> [ArchSegmentOff arch]
                    -> DiscoveryState arch
                    -> DiscoveryState arch
markAddrsAsFunction rsn addrs s0 = foldl' (\s a -> markAddrAsFunction rsn a s) s0 addrs

------------------------------------------------------------------------
-- FoundAddr

-- | An address that has been found to be reachable.
data FoundAddr arch
   = FoundAddr { foundReason :: !(CodeAddrReason (ArchAddrWidth arch))
                 -- ^ The reason the address was found to be containing code.
               , foundAbstractState :: !(AbsBlockState (ArchReg arch))
                 -- ^ The abstract state formed from post-states that reach this address.
               }

foundReasonL :: Lens' (FoundAddr arch) (CodeAddrReason (ArchAddrWidth arch))
foundReasonL = lens foundReason (\old new -> old { foundReason = new })

------------------------------------------------------------------------
-- FunState

-- | The state for the function exploration monad (funM)
data FunState arch s ids
   = FunState { funNonceGen  :: !(NonceGenerator (ST s) ids)
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
  :: MemWidth (RegAddrWidth (ArchReg arch))
  => ArchSegmentOff arch
  -> ParsedBlock arch ids
  -> FunState arch s ids
  -> FunState arch s ids
addFunBlock segment block s = case Map.lookupLT segment (s ^. curFunBlocks) of
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
mergeIntraJump  :: MemWidth (ArchAddrWidth arch)
                => ArchSegmentOff arch
                  -- ^ Source label that we are jumping from.
                -> AbsBlockState (ArchReg arch)
                   -- ^ The state of the system after jumping to new block.
                -> ArchSegmentOff arch
                   -- ^ Address we are trying to reach.
                -> FunM arch s ids ()
mergeIntraJump src ab tgt = do
-- trace ("mergeIntraJump " ++ show src ++ " " ++ show tgt) $ do
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
-- Jump table bounds

-- | Figure out if this is a jump table.
matchJumpTable :: MemWidth (ArchAddrWidth arch)
               => Memory (ArchAddrWidth arch)
               -> BVValue arch ids (ArchAddrWidth arch) -- ^ Memory address that IP is read from.
               -> Maybe (ArchSegmentOff arch, BVValue arch ids (ArchAddrWidth arch))
matchJumpTable mem read_addr
    -- Turn the read address into base + offset.
  | Just (BVAdd _ offset base_val) <- valueAsApp read_addr
  , Just mseg <- valueAsSegmentOff mem base_val
    -- Turn the offset into a multiple by an index.
  , Just (BVMul _ (BVValue _ mul) jump_index) <- valueAsApp offset
  , mul == toInteger (addrSize (memAddrWidth mem))
  , Perm.isReadonly (segmentFlags (msegSegment mseg)) = do
    Just (mseg, jump_index)
matchJumpTable _ _ =
    Nothing

-- | This describes why we could not infer the bounds of code that looked like it
-- was accessing a jump table.
data JumpTableBoundsError arch ids
   = CouldNotInterpretAbsValue !(AbsValue (ArchAddrWidth arch) (BVType (ArchAddrWidth arch)))
   | UpperBoundMismatch !(Jmp.UpperBound (BVType (ArchAddrWidth arch))) !Integer
   | CouldNotFindBound String !(ArchAddrValue arch ids)

-- | Show the jump table bounds
showJumpTableBoundsError :: ArchConstraints arch => JumpTableBoundsError arch ids -> String
showJumpTableBoundsError err =
  case err of
    CouldNotInterpretAbsValue val ->
      "Index interval is not a stride " ++ show val
    UpperBoundMismatch bnd index_range ->
      "Upper bound mismatch at jumpbounds "
                ++ show bnd
                ++ " domain "
                ++ show index_range
    CouldNotFindBound msg jump_index ->
      show "Could not find  jump table: " ++ msg ++ "\n"
      ++ show (ppValueAssignments jump_index)

-- | Returns the index bounds for a jump table of 'Nothing' if this is
-- not a block table.
getJumpTableBounds :: ArchitectureInfo a
                   -> AbsProcessorState (ArchReg a) ids -- ^ Current processor registers.
                   -> ArchSegmentOff a -- ^ Base
                   -> BVValue a ids (ArchAddrWidth a) -- ^ Index in jump table
                   -> Either (JumpTableBoundsError a ids) (ArchAddrWord a)
                   -- ^ One past last index in jump table or nothing
getJumpTableBounds info regs base jump_index = withArchConstraints info $
  case transferValue regs jump_index of
    StridedInterval (SI.StridedInterval _ index_base index_range index_stride) -> do
      let index_end = index_base + (index_range + 1) * index_stride
      if rangeInReadonlySegment base (jumpTableEntrySize info * fromInteger index_end) then
        case Jmp.unsignedUpperBound (regs^.indexBounds) jump_index of
          Right (Jmp.IntegerUpperBound bnd) | bnd == index_range -> Right $! fromInteger index_end
          Right bnd -> Left (UpperBoundMismatch bnd index_range)
          Left  msg -> Left (CouldNotFindBound  msg jump_index)
       else
        error $ "Jump table range is not in readonly memory"
    abs_value -> Left (CouldNotInterpretAbsValue abs_value)

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
          let addrs = concretizeAbsCodePointers mem (transferValue regs v)
          writtenCodeAddrs %= (addrs ++)
    _ -> return ()


------------------------------------------------------------------------
-- ParseContext

-- | Information needed to parse the processor state
data ParseContext arch ids =
  ParseContext { pctxMemory         :: !(Memory (ArchAddrWidth arch))
               , pctxArchInfo       :: !(ArchitectureInfo arch)
               , pctxKnownFnEntries :: !(Set (ArchSegmentOff arch))
                 -- ^ Entry addresses for known functions (e.g. from symbol information)
               , pctxTrustKnownFns  :: !Bool
                 -- ^ should we use pctxKnownFns in analysis to identify e.g. jump vs. tail calls
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
                    => AbsProcessorState (ArchReg arch) ids
                       -- ^ Abstract processor state just before call.
                    -> BVValue arch ids (ArchAddrWidth arch)
                    -> [ArchSegmentOff arch]
identifyCallTargets absState ip = do
  -- Code pointers from abstract domains.
  let mem = absMem absState
  let def = concretizeAbsCodePointers mem (transferValue absState ip)
  let segOffAddrs :: Maybe (ArchSegmentOff arch) -> [ArchSegmentOff arch]
      segOffAddrs (Just addr)
        | segmentFlags (msegSegment addr) `Perm.hasPerm` Perm.execute =
            [addr]
      segOffAddrs _ = []
  case ip of
    BVValue _ x -> segOffAddrs $ resolveAbsoluteAddr mem (fromInteger x)
    RelocatableValue _ a -> segOffAddrs $ asSegmentOff mem a
    AssignedValue a ->
      case assignRhs a of
        -- See if we can get a value out of a concrete memory read.
        ReadMem addr (BVMemRepr _ end)
          | Just laddr <- valueAsMemAddr addr
          , Right val <- readAddr mem end laddr ->
            segOffAddrs (asSegmentOff mem val) ++ def
        _ -> def
    Initial _ -> def

-- | This parses a block that ended with a fetch and execute instruction.
parseFetchAndExecute :: forall arch ids
                     .  ParseContext arch ids
                     -> Word64
                        -- ^ Index of this block
                     -> [Stmt arch ids]
                     -> AbsProcessorState (ArchReg arch) ids
                     -- ^ Registers prior to blocks being executed.
                     -> RegState (ArchReg arch) (Value arch ids)
                     -> State (ParseState arch ids) (StatementList arch ids)
parseFetchAndExecute ctx lbl_idx stmts regs s' = do
  let src = pctxAddr ctx
  withArchConstraints arch_info $ do
  -- See if next statement appears to end with a call.
  -- We define calls as statements that end with a write that
  -- stores the pc to an address.
  let absProcState' = absEvalStmts arch_info regs stmts
  case () of
    -- The last statement was a call.
    -- Note that in some cases the call is known not to return, and thus
    -- this code will never jump to the return value.
    _ | Just (prev_stmts, ret) <- identifyCall arch_info mem stmts s'  -> do
        mapM_ (recordWriteStmt arch_info mem absProcState') prev_stmts
        let abst = finalAbsBlockState absProcState' s'
        seq abst $ do
        -- Merge caller return information
        intraJumpTargets %= ((ret, postCallAbsState arch_info abst ret):)
        -- Use the abstract domain to look for new code pointers for the current IP.
        let addrs = identifyCallTargets absProcState' (s'^.boundValue ip_reg)
        newFunctionAddrs %= (++ addrs)
        -- Use the call-specific code to look for new IPs.

        pure StatementList { stmtsIdent = lbl_idx
                           , stmtsNonterm = toList prev_stmts
                           , stmtsTerm  = ParsedCall s' (Just ret)
                           , stmtsAbsState = absProcState'
                           }

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
      | Just (prev_stmts) <- identifyReturn arch_info stmts s' absProcState' -> do
        mapM_ (recordWriteStmt arch_info mem absProcState') prev_stmts

        pure StatementList { stmtsIdent = lbl_idx
                           , stmtsNonterm = toList prev_stmts
                           , stmtsTerm = ParsedReturn s'
                           , stmtsAbsState = absProcState'
                           }

      -- Jump to a block within this function.
      | Just tgt_mseg <- asSegmentOff mem =<< valueAsMemAddr (s'^.boundValue ip_reg)
      , segmentFlags (msegSegment tgt_mseg) `Perm.hasPerm` Perm.execute
        -- The target address cannot be this function entry point.
        --
        -- This will result in the target being treated as a call or tail call.
      , tgt_mseg /= pctxFunAddr ctx

      -- If we are trusting known function entries, then only mark as an
      -- intra-procedural jump if the target is not a known function entry.
      , not (pctxTrustKnownFns ctx) || (tgt_mseg `notElem` pctxKnownFnEntries ctx) -> do

         mapM_ (recordWriteStmt arch_info mem absProcState') stmts
         -- Merge block state and add intra jump target.
         let abst = finalAbsBlockState absProcState' s'
         let abst' = abst & setAbsIP tgt_mseg
         intraJumpTargets %= ((tgt_mseg, abst'):)
         pure StatementList { stmtsIdent = lbl_idx
                            , stmtsNonterm = stmts
                            , stmtsTerm  = ParsedJump s' tgt_mseg
                            , stmtsAbsState = absProcState'
                            }
      -- Block ends with what looks like a jump table.
      | AssignedValue (Assignment _ (ReadMem ptr _)) <- debug DCFG "try jump table" $ s'^.curIP
        -- Attempt to compute interval of addresses interval is over.
      , Just (base, jump_idx) <- matchJumpTable mem ptr ->
        case getJumpTableBounds arch_info absProcState' base jump_idx of
          Left err ->
            trace (show src ++ ": Could not compute bounds: " ++ showJumpTableBoundsError err) $ do
            mapM_ (recordWriteStmt arch_info mem absProcState') stmts
            pure StatementList { stmtsIdent = lbl_idx
                               , stmtsNonterm = stmts
                               , stmtsTerm  = ClassifyFailure s'
                               , stmtsAbsState = absProcState'
                               }
          Right read_end -> do
            mapM_ (recordWriteStmt arch_info mem absProcState') stmts

            -- Try to compute jump table bounds

            let abst :: AbsBlockState (ArchReg arch)
                abst = finalAbsBlockState absProcState' s'
            seq abst $ do
            -- This function resolves jump table entries.
            -- It is a recursive function that has an index into the jump table.
            -- If the current index can be interpreted as a intra-procedural jump,
            -- then it will add that to the current procedure.
            -- This returns the last address read.
            let resolveJump :: [ArchSegmentOff arch]
                               -- /\ Addresses in jump table in reverse order
                            -> ArchAddrWord arch
                               -- /\ Current index
                            -> State (ParseState arch ids) [ArchSegmentOff arch]
                resolveJump prev idx | idx == read_end = do
                  -- Stop jump table when we have reached computed bounds.
                  return (reverse prev)
                resolveJump prev idx = do
                  let read_addr = relativeSegmentAddr base & incAddr (toInteger (8 * idx))
                  case readAddr mem (archEndianness arch_info) read_addr of
                      Right tgt_addr
                        | Just read_mseg <- asSegmentOff mem read_addr
                        , Perm.isReadonly (segmentFlags (msegSegment read_mseg))
                        , Just tgt_mseg <- asSegmentOff mem tgt_addr
                        , Perm.isExecutable (segmentFlags (msegSegment tgt_mseg)) -> do
                          let abst' = abst & setAbsIP tgt_mseg
                          intraJumpTargets %= ((tgt_mseg, abst'):)
                          resolveJump (tgt_mseg:prev) (idx+1)
                      _ -> do
                        debug DCFG ("Stop jump table: " ++ show idx ++ " " ++ show read_end) $ do
                          return (reverse prev)
            read_addrs <- resolveJump [] 0
            pure StatementList { stmtsIdent = lbl_idx
                               , stmtsNonterm = stmts
                               , stmtsTerm = ParsedLookupTable s' jump_idx (V.fromList read_addrs)
                               , stmtsAbsState = absProcState'
                               }

      -- Check for tail call (anything where we are right at stack height)
      --
      -- TODO: this makes sense for x86, but is not correct for all architectures
      | ptrType    <- addrMemRepr arch_info
      , sp_val     <- s'^.boundValue sp_reg
      , ReturnAddr <- absEvalReadMem absProcState' sp_val ptrType ->
        finishWithTailCall absProcState'

      -- Is this a jump to a known function entry? We're already past the
      -- "identifyCall" case, so this must be a tail call, assuming we trust our
      -- known function entry info.
      | pctxTrustKnownFns ctx
      , Just tgt_mseg <- valueAsSegmentOff mem (s'^.boundValue ip_reg)
      , tgt_mseg `elem` pctxKnownFnEntries ctx ->
        finishWithTailCall absProcState'

      -- Block that ends with some unknown
      | otherwise -> do
          mapM_ (recordWriteStmt arch_info mem absProcState') stmts
          pure StatementList { stmtsIdent = lbl_idx
                             , stmtsNonterm = stmts
                             , stmtsTerm  = ClassifyFailure s'
                             , stmtsAbsState = absProcState'
                             }

  where mem = pctxMemory ctx
        arch_info = pctxArchInfo ctx

        finishWithTailCall :: RegisterInfo (ArchReg arch)
                           => AbsProcessorState (ArchReg arch) ids
                           -> State (ParseState arch ids) (StatementList arch ids)
        finishWithTailCall absProcState' = do
          mapM_ (recordWriteStmt arch_info mem absProcState') stmts

          -- Compute final state
          let abst = finalAbsBlockState absProcState' s'
          seq abst $ do

          -- Look for new instruction pointers
          let addrs = concretizeAbsCodePointers mem (abst^.absRegState^.curIP)
          newFunctionAddrs %= (++ addrs)

          pure StatementList { stmtsIdent = lbl_idx
                             , stmtsNonterm = stmts
                             , stmtsTerm  = ParsedCall s' Nothing
                             , stmtsAbsState = absProcState'
                             }


-- | this evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
parseBlock :: ParseContext arch ids
              -- ^ Context for parsing blocks.
           -> Block arch ids
              -- ^ Block to parse
           -> AbsProcessorState (ArchReg arch) ids
              -- ^ Abstract state at start of block
           -> State (ParseState arch ids) (StatementList arch ids)
parseBlock ctx b regs = do
  let mem       = pctxMemory ctx
  let arch_info = pctxArchInfo ctx
  withArchConstraints arch_info $ do
  let idx = blockLabel b
  let block_map = pctxBlockMap ctx
  -- FIXME: we should propagate c back to the initial block, not just b
  let absProcState' = absEvalStmts arch_info regs (blockStmts b)
  case blockTerm b of
    Branch c lb rb -> do
      mapM_ (recordWriteStmt arch_info mem absProcState') (blockStmts b)

      let Just l = Map.lookup lb block_map
      let l_regs = refineProcStateBounds c True $ refineProcState c absTrue absProcState'
      let Just r = Map.lookup rb block_map
      let r_regs = refineProcStateBounds c False $ refineProcState c absFalse absProcState'

      let l_regs' = absEvalStmts arch_info l_regs (blockStmts b)
      let r_regs' = absEvalStmts arch_info r_regs (blockStmts b)

      parsedTrueBlock  <- parseBlock ctx l l_regs'
      parsedFalseBlock <- parseBlock ctx r r_regs'

      pure $! StatementList { stmtsIdent = idx
                            , stmtsNonterm = blockStmts b
                            , stmtsTerm  = ParsedIte c parsedTrueBlock parsedFalseBlock
                            , stmtsAbsState = absProcState'
                            }

    FetchAndExecute s' -> do
      parseFetchAndExecute ctx idx (blockStmts b) regs s'

    -- Do nothing when this block ends in a translation error.
    TranslateError _ msg -> do
      pure $! StatementList { stmtsIdent = idx
                            , stmtsNonterm = blockStmts b
                            , stmtsTerm = ParsedTranslateError msg
                            , stmtsAbsState = absProcState'
                            }
    ArchTermStmt ts s' -> do
      mapM_ (recordWriteStmt arch_info mem absProcState') (blockStmts b)
      let abst = finalAbsBlockState absProcState' s'
      -- Compute possible next IPS.
      let r = postArchTermStmtAbsState arch_info mem abst s' ts
      case r of
        Just (addr,post) ->
          intraJumpTargets %= ((addr, post):)
        Nothing -> pure ()
      pure $! StatementList { stmtsIdent = idx
                            , stmtsNonterm = blockStmts b
                            , stmtsTerm  = ParsedArchTermStmt ts s' (fst <$> r)
                            , stmtsAbsState = absProcState'
                            }

-- | This evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
transferBlocks :: MemWidth (RegAddrWidth (ArchReg arch))
               => ArchSegmentOff arch
                  -- ^ Address of theze blocks
               -> FoundAddr arch
                  -- ^ State leading to explore block
               -> ArchAddrWord arch
                  -- ^ Size of the region these blocks cover.
               -> Map Word64 (Block arch ids)
                  -- ^ Map from labelIndex to associated block
               -> FunM arch s ids ()
transferBlocks src finfo sz block_map =
  case Map.lookup 0 block_map of
    Nothing -> do
      error $ "transferBlocks given empty blockRegion."
    Just b -> do
      mem       <- uses curFunCtx memory
      let regs = initAbsProcessorState mem (foundAbstractState finfo)
      funAddr <- gets curFunAddr
      s <- use curFunCtx

      -- Combine entries of functions we've discovered thus far with
      -- undiscovered functions with entries marked InitAddr, which we assume is
      -- info we know from the symbol table or some other reliable source, and
      -- pass in. Only used in analysis if pctxTrustKnownFns is True.
      let knownFns = Set.union (Map.keysSet $ s^.funInfo)
                               (Map.keysSet $ Map.filter (== InitAddr) $ s^.unexploredFunctions)
      let ctx = ParseContext { pctxMemory         = memory s
                             , pctxArchInfo       = archInfo s
                             , pctxKnownFnEntries = knownFns
                             , pctxTrustKnownFns  = s^.trustKnownFns
                             , pctxFunAddr        = funAddr
                             , pctxAddr           = src
                             , pctxBlockMap       = block_map
                             }
      let ps0 = ParseState { _writtenCodeAddrs = []
                           , _intraJumpTargets = []
                           , _newFunctionAddrs = []
                           }
      let (pblock, ps) = runState (parseBlock ctx b regs) ps0
      let pb = ParsedBlock { pblockAddr = src
                           , blockSize = sz
                           , blockReason = foundReason finfo
                           , blockAbstractState = foundAbstractState finfo
                           , blockStatementList = pblock
                           }
      id %= addFunBlock src pb
      curFunCtx %= markAddrsAsFunction (InWrite src)    (ps^.writtenCodeAddrs)
                .  markAddrsAsFunction (CallTarget src) (ps^.newFunctionAddrs)
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
  let seg = msegSegment addr
      off = msegOffset addr
  let max_size =
        case Map.lookupGT addr prev_block_map of
          Just (next,_) | Just o <- diffSegmentOff next addr -> fromInteger o
          _ -> segmentSize seg - off
  let ab = foundAbstractState finfo
  (bs0, sz, maybeError) <- liftST $ do
#ifdef USE_REWRITER
    disassembleAndRewrite ainfo mem nonceGen addr max_size ab
#else
    disassembleFn ainfo mem nonceGen addr max_size ab
#endif

  -- If no blocks are returned, then we just add an empty parsed block.
  if null bs0 then do
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
    let bs = eliminateDeadStmts ainfo bs0
    -- Call transfer blocks to calculate parsedblocks
    let block_map = Map.fromList [ (blockLabel b, b) | b <- bs ]
    transferBlocks addr finfo sz block_map

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
           -> CodeAddrReason (ArchAddrWidth arch)
              -- ^ Reason to provide for why we are analyzing this function
              --
              -- This can be used to figure out why we decided a
              -- given address identified a code location.
           -> ArchSegmentOff arch
           -> FunState arch s ids
mkFunState gen s rsn addr = do
  let faddr = FoundAddr { foundReason = rsn
                        , foundAbstractState = mkInitialAbsState (archInfo s) (memory s) addr
                        }
   in FunState { funNonceGen = gen
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
      info = archInfo s
      nm = withArchConstraints info $
         fromMaybe (BSC.pack (show addr)) (Map.lookup addr (symbolNames s))
   in DiscoveryFunInfo { discoveredFunAddr = addr
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
                -> CodeAddrReason (ArchAddrWidth arch)
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
      seq finfo $ seq s' $ pure (s', Some finfo)

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
  =  segmentFlags (msegSegment a) `Perm.hasPerm` Perm.write
  && segmentFlags (msegSegment v) `Perm.hasPerm` Perm.execute

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
  -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
  -> DiscoveryState arch
cfgFromAddrs arch_info mem symbols =
  cfgFromAddrsAndState (emptyDiscoveryState mem symbols arch_info)

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

------------------------------------------------------------------------
-- Resolve functions with logging

resolveFuns :: MemWidth (RegAddrWidth (ArchReg arch))
            => (ArchSegmentOff arch -> CodeAddrReason (ArchAddrWidth arch) -> ST s Bool)
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
                        -- memory after exploring other potnetial
                        -- functions.
                      , logAtAnalyzeFunction  :: !Bool
                      -- ^ Print a message each time we apply
                      -- discovery analysis to a new function.
                      , logAtAnalyzeBlock     :: !Bool
                      -- ^ Print a message each time we analyze a
                      -- block within a function.
                     }

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

-- | Explore until we have found all functions we can.
--
-- This function is intended to make it easy to explore functions, and
-- can be controlled via 'DiscoveryOptions'.
completeDiscoveryState :: forall arch
                       .  ArchitectureInfo arch
                       -> DiscoveryOptions
                          -- ^ Options controlling discovery
                       -> Memory (ArchAddrWidth arch)
                          -- ^ Memory state used for static code discovery.
                       -> [MemSegmentOff (ArchAddrWidth arch)]
                          -- ^ Initial entry points to explore
                       -> AddrSymMap (ArchAddrWidth arch)
                          -- ^ The map from addresses to symbols
                       -> (ArchSegmentOff arch -> Bool)
                          -- ^ Predicate to check if we should explore a function
                          --
                          -- Return true to explore all functions.
                       -> IO (DiscoveryState arch)
completeDiscoveryState ainfo disOpt mem initEntries symMap funPred = stToIO $ withArchConstraints ainfo $ do
  let initState
        = emptyDiscoveryState mem symMap ainfo
        & markAddrsAsFunction InitAddr initEntries
  -- Add symbol table entries to discovery state if requested
  let postSymState
        | exploreFunctionSymbols disOpt =
            initState & markAddrsAsFunction InitAddr (Map.keys symMap)
        | otherwise = initState
  let analyzeFn addr _rsn = ioToST $ do
        let b = funPred addr
        when (b && logAtAnalyzeFunction disOpt) $ do
          hPutStrLn stderr $ "Analyzing function: " ++ ppSymbol addr symMap
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
    let mem_contents = withArchConstraints ainfo $ memAsAddrPairs mem LittleEndian
    resolveFuns analyzeFn analyzeBlock $ postPhase1Discovery & exploreMemPointers mem_contents
   else
    return postPhase1Discovery
