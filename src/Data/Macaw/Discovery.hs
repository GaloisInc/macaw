{- |
Module           : Reopt.Semantics.CFGDiscovery
Copyright        : (c) Galois, Inc 2015-2016
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This contains an implementation of a CFG discovery algorithm based upon an
interleaved abstract interpretation.
-}
{-# LANGUAGE ConstraintKinds #-}
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
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.Discovery
       ( cfgFromAddrs
       , assignmentAbsValues
       ) where

import           Control.Exception
import           Control.Lens
import           Control.Monad.ST
import           Control.Monad.State.Strict
import qualified Data.ByteString.Char8 as BSC
import           Data.Char (isDigit)
import qualified Data.Foldable as Fold
import           Data.List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Word
import           Numeric

import           Debug.Trace

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.AbsDomain.Refine
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.DebugLogging
import           Data.Macaw.Discovery.Info
import           Data.Macaw.Memory
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

-- Get the absolute value associated with an address.
transferReadMem :: (OrdF (ArchReg a), ShowF (ArchReg a), MemWidth (RegAddrWidth (ArchReg a)))
                => AbsProcessorState (ArchReg a) ids
                -> ArchAddrValue a ids
                -> MemRepr tp
                   -- ^ Information about the memory layout for the value.
                -> ArchAbsValue a tp
transferReadMem r a tp
  | StackOffset _ s <- transferValue r a
  , [o] <- Set.toList s
  , Just (StackEntry v_tp v) <- Map.lookup o (r^.curAbsStack)
  , Just Refl <- testEquality tp v_tp = v
  | otherwise = TopV

-- | Get the abstract domain for the right-hand side of an assignment.
transferRHS :: forall a ids tp
            .  ( OrdF (ArchReg a)
               , ShowF (ArchReg a)
               , MemWidth (ArchAddrWidth a)
               )
            => ArchitectureInfo a
            -> AbsProcessorState (ArchReg a) ids
            -> AssignRhs a ids tp
            -> ArchAbsValue a tp
transferRHS info r rhs =
  case rhs of
    EvalApp app    -> transferApp r app
    SetUndefined _ -> TopV
    ReadMem a tp   -> transferReadMem r a tp
    EvalArchFn f _ -> absEvalArchFn info r f

-- | Merge in the value of the assignment.
--
-- If we have already seen a value, this will combine with meet.
addAssignment :: ( OrdF  (ArchReg a)
                 , ShowF (ArchReg a)
                 , MemWidth (ArchAddrWidth a)
                 )
              => ArchitectureInfo a
              -> Assignment a ids tp
              -> AbsProcessorState (ArchReg a) ids
              -> AbsProcessorState (ArchReg a) ids
addAssignment info a c =
  c & (absAssignments . assignLens (assignId a))
    %~ flip meet (transferRHS info c (assignRhs a))

------------------------------------------------------------------------
-- Utilities

-- | Get code pointers out of a abstract value.
concretizeAbsCodePointers :: MemWidth w
                          => Memory w
                          -> AbsValue w (BVType w)
                          -> [SegmentedAddr w]
concretizeAbsCodePointers mem (FinSet s) =
  [ sa
  | a <- Set.toList s
  , Just sa <- [absoluteAddrSegment mem (fromInteger a)]
  , Perm.isExecutable (segmentFlags (addrSegment sa))
  ]
concretizeAbsCodePointers _ (CodePointers s _) =
  [ sa
  | sa <- Set.toList s
  , Perm.isExecutable (segmentFlags (addrSegment sa))
  ]
  -- FIXME: this is dangerous !!
concretizeAbsCodePointers _mem StridedInterval{} = [] -- FIXME: this case doesn't make sense
  -- debug DCFG ("I think these are code pointers!: " ++ show s) $ []
  -- filter (isCodeAddr mem) $ fromInteger <$> SI.toList s
concretizeAbsCodePointers _mem _ = []

{-
printAddrBacktrace :: Map (ArchSegmentedAddr arch) (FoundAddr arch)
                   -> ArchSegmentedAddr arch
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
    InterProcedureJump src -> pp ("Reference from external address " ++ show src ++ ".") : prev src

-- | Return true if this address was added because of the contents of a global address
-- in memory initially.
--
-- This heuristic is not very accurate, so we avoid printing errors when it leads to
-- issues.
cameFromUnsoundReason :: Map (ArchSegmentedAddr arch) (FoundAddr arch)
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
    InterProcedureJump src -> prev src
-}

------------------------------------------------------------------------
-- Memory utilities

-- | Return true if range is entirely contained within a single read only segment.Q
rangeInReadonlySegment :: MemWidth w
                       => SegmentedAddr w -- ^ Start of range
                       -> MemWord w -- ^ The size of the range
                       -> Bool
rangeInReadonlySegment base size
    = base^.addrOffset + size <= segmentSize seg
    && Perm.isReadonly (segmentFlags seg)
  where seg = addrSegment base


------------------------------------------------------------------------
-- CFGM

-- | The CFG-building monad: includes a state component with a 'DiscoveryInfo'
-- and a 'NonceGenerator', layered on top of the 'ST' monad
newtype CFGM arch ids a =
    CFGM { unCFGM :: StateT (DiscoveryInfo arch ids) (ST ids) a }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadState (DiscoveryInfo arch ids)
           )

-- | Run a CFGM at the top level
runCFGM :: ArchitectureInfo arch
           -- ^ Architecture-specific information needed for doing control-flow exploration.
        -> Memory (ArchAddrWidth arch)
           -- ^ Memory to use when decoding instructions.
        -> Map (ArchSegmentedAddr arch) BSC.ByteString
           -- ^ Names for (some) function entry points
        -> (forall ids . CFGM arch ids ())
           -- ^ Computation to run.
        -> Some (DiscoveryInfo arch)
runCFGM arch_info mem symbols m = do
  withGlobalSTNonceGenerator $ \nonce_gen -> do
    let init_info = emptyDiscoveryInfo nonce_gen mem symbols arch_info
    Some <$> execStateT (unCFGM m) init_info

------------------------------------------------------------------------
-- FunM

data FunState arch ids
   = FunState {  curFunAddr :: !(ArchSegmentedAddr arch)
              , _curFunInfo :: !(DiscoveryFunInfo arch ids)
                 -- ^ Information about current function we are working on
              , _frontier :: !(Set (ArchSegmentedAddr arch))
                 -- ^ Addresses to explore next.
              }

-- | Information about current function we are working on
curFunInfo :: Simple Lens (FunState arch ids)  (DiscoveryFunInfo arch ids)
curFunInfo = lens _curFunInfo (\s v -> s { _curFunInfo = v })

-- | Set of addresses to explore next.
--
-- This is a map so that we can associate a reason why a code address
-- was added to the frontier.
frontier :: Simple Lens (FunState arch ids)  (Set (ArchSegmentedAddr arch))
frontier = lens _frontier (\s v -> s { _frontier = v })

-- | A newtype around a function
newtype FunM arch ids a = FunM { unFunM :: StateT (FunState arch ids) (CFGM arch ids) a }
  deriving (Functor, Applicative, Monad)

instance MonadState (FunState arch ids) (FunM arch ids) where
  get = FunM $ get
  put s = FunM $ put s

liftCFG :: CFGM arch ids a -> FunM arch ids a
liftCFG m = FunM (lift m)

liftST :: ST ids a -> CFGM arch ids a
liftST = CFGM . lift

------------------------------------------------------------------------
-- Block discovery

{-
-- | This is the worker for getBlock, in the case that we have not already
-- read the block.
tryDisassembleAddr :: ArchConstraints arch
                   => ArchSegmentedAddr arch
                      -- ^ Address to disassemble
                   -> AbsBlockState (ArchReg arch)
                      -- ^ Abstract state at beginning of block
                   -> CFGM arch ids ()
tryDisassembleAddr addr ab = do
  s0 <- get
  -- Attempt to disassemble block.
  -- Get memory so that we can decode from it.
  let block_addrs = s0^.blocks
  -- Returns true if we are not at the start of a block.
  -- This is used to stop the disassembler when we reach code
  -- that is part of a new block.
  let not_at_block = (`Map.notMember` block_addrs)
  let mem = memory s0
  let nonce_gen = nonceGen s0
  (bs, next_ip, maybeError) <- liftST $ disassembleFn (archInfo s0) nonce_gen mem not_at_block addr ab
  -- Build state for exploring this.
  case maybeError of
    Just e -> do
      trace ("Failed to disassemble " ++ show e) $ pure ()
    Nothing -> do
      pure ()

  assert (segmentIndex (addrSegment next_ip) == segmentIndex (addrSegment addr)) $ do
  assert (next_ip^.addrOffset > addr^.addrOffset) $ do
  let block_map = Map.fromList [ (labelIndex (blockLabel b), b) | b <- bs ]
  -- Add block region to blocks.
  let br = BlockRegion { brSize = next_ip^.addrOffset - addr^.addrOffset
                       , brBlocks = block_map
                       }
  put $! s0 & blocks     %~ Map.insert addr br
-}

{-
-- | Mark address as the start of a code block.
markCodeAddrBlock :: ArchConstraints arch
                  => CodeAddrReason (ArchAddrWidth arch)
                      -- ^ Reason we are trying to disassemble starting from given address
                  -> ArchSegmentedAddr arch
                     -- ^ Address to start disassembling
                  -> AbsBlockState (ArchReg arch)
                     -- ^ Abstract block state at start of disassembly
                  -> CFGM arch ids ()
markCodeAddrBlock rsn addr ab = do
  s <- get
  -- Lookup block just before this address
  case Map.lookupLT addr (s^.blocks) of
    -- If that block overlaps with the address
    Just (l, br)
      | segmentIndex (addrSegment addr) == segmentIndex (addrSegment l)
      , addr^.addrOffset < l^.addrOffset + brSize br -> do
      -- Get block for addr
      tryDisassembleAddr addr ab
      -- Get block for old block
      case Map.lookup l (s^.foundAddrs) of
        Just info ->
          tryDisassembleAddr l (foundAbstractState info)
        Nothing -> error $ "Internal mark code addr as block saved but no reason information stored."
      -- It's possible this will cause the current block to be broken, or cause a function to
      -- boundaries.  However, we don't think this should cause the need automatically to
      -- re-evaluate a block as any information discovered should be strictly less than
      -- the longer block.
    _ -> do
      tryDisassembleAddr addr ab
-}

------------------------------------------------------------------------
-- Transfer stmts

transferStmt :: ( RegisterInfo (ArchReg arch)
                , HasRepr (ArchReg arch) TypeRepr
                , MemWidth (ArchAddrWidth arch)
                )
             => ArchitectureInfo arch
             -> Stmt arch ids
             -> State (AbsProcessorState (ArchReg arch) ids) ()
transferStmt info stmt =
  case stmt of
    AssignStmt a -> do
      modify $ addAssignment info a
    WriteMem addr memRepr v -> do
      modify $ \r -> addMemWrite (r^.absInitialRegs^.curIP) addr memRepr v r
    _ -> return ()

newtype HexWord = HexWord Word64

instance Show HexWord where
  showsPrec _ (HexWord w) = showHex w

-- | Mark a escaped code pointer as a function entry.
markAddrAsFunction :: ArchConstraints arch
                   => CodeAddrReason (ArchAddrWidth arch)
                   -> ArchSegmentedAddr arch
                   -> CFGM arch ids ()
markAddrAsFunction rsn addr = do
  s <- get
  when (not (Set.member addr (s^.functionEntries))) $ do
    let _high = Set.lookupGT addr (s^.functionEntries)
    modify $ (functionEntries   %~ Set.insert addr)
           . (function_frontier %~ Map.insert addr rsn)

transferStmts :: ( HasRepr      (ArchReg arch) TypeRepr
                 , RegisterInfo (ArchReg arch)
                 , MemWidth (ArchAddrWidth arch)
                 )
              => ArchitectureInfo arch
              -> AbsProcessorState (ArchReg arch) ids
              -> [Stmt arch ids]
              -> AbsProcessorState (ArchReg arch) ids
transferStmts info r stmts = execState (mapM_ (transferStmt info) stmts) r

-- | Generate map that maps each assignment in the CFG to the abstract value
-- associated with it.
assignmentAbsValues :: forall arch ids
                    .  ( HasRepr      (ArchReg arch) TypeRepr
                       , RegisterInfo (ArchReg arch)
                       , MemWidth (ArchAddrWidth arch)
                       )
                    => ArchitectureInfo arch
                    -> Memory (ArchAddrWidth arch)
                    -> CFG arch ids
                    -> Map (ArchSegmentedAddr arch) (AbsBlockState (ArchReg arch))
                       -- ^ Maps addresses to the initial state at that address.
                    -> MapF (AssignId ids) (ArchAbsValue arch)
assignmentAbsValues info mem g absm =
     foldl' go MapF.empty (Map.elems (g^.cfgBlocks))
  where go :: MapF (AssignId ids) (ArchAbsValue arch)
           -> Block arch ids
           -> MapF (AssignId ids) (ArchAbsValue arch)
        go m0 b =
          case blockLabel b of
            GeneratedBlock a 0 -> do
              case Map.lookup a absm of
                Nothing -> do
                  error $ "internal: assignmentAbsValues could not find code infomation for block " ++ show a
                Just blockState -> do
                  let abs_state = initAbsProcessorState mem blockState
                  insBlock b abs_state m0
            _ -> m0

        insBlock :: Block arch ids
                 -> AbsProcessorState (ArchReg arch) ids
                 -> MapF (AssignId ids) (ArchAbsValue arch)
                 -> MapF (AssignId ids) (ArchAbsValue arch)
        insBlock b r0 m0 =
          let final = transferStmts info r0 (blockStmts b)
              m = MapF.union (final^.absAssignments) m0 in
          case blockTerm b of
            Branch _ lb rb -> do
              let Just l = findBlock g lb
              let Just r = findBlock g rb
              insBlock l final $
                insBlock r final $
                m
            FetchAndExecute _ -> m
            Syscall _ -> m
            TranslateError{} -> m

------------------------------------------------------------------------
-- Transfer functions

-- | Joins in the new abstract state and returns the locations for
-- which the new state is changed.
mergeIntraJump  :: ArchConstraints arch
                => ArchSegmentedAddr arch
                  -- ^ Source label that we are jumping from.
                -> AbsBlockState (ArchReg arch)
                   -- ^ Block state after executing instructions.
                -> ArchSegmentedAddr arch
                   -- ^ Address we are trying to reach.
                -> FunM arch ids ()
mergeIntraJump src ab _tgt
  | not (absStackHasReturnAddr ab)
  , debug DCFG ("WARNING: Missing return value in jump from " ++ show src ++ " to\n" ++ show ab) False
  = error "internal: Unexpected mergeIntraJump"
mergeIntraJump src ab tgt = do
  let rsn = NextIP src
  -- Associate a new abstract state with the code region.
  s0 <- use curFunInfo
  case Map.lookup tgt (s0^.foundAddrs) of
    -- We have seen this block before, so need to join and see if
    -- the results is changed.
    Just old_info -> do
      case joinD (foundAbstractState old_info) ab of
        Nothing  -> return ()
        Just new -> do
          let new_info = old_info { foundAbstractState = new }
          curFunInfo . foundAddrs   %= Map.insert tgt new_info
          curFunInfo . reverseEdges %= Map.insertWith Set.union tgt (Set.singleton src)
          frontier %= Set.insert tgt
    -- We haven't seen this block before
    Nothing -> do
      curFunInfo . reverseEdges %= Map.insertWith Set.union tgt (Set.singleton src)
      frontier     %= Set.insert tgt
--      liftCFG $ markCodeAddrBlock rsn tgt ab
      let found_info = FoundAddr { foundReason = rsn
                                 , foundAbstractState = ab
                                 }
      curFunInfo . foundAddrs %= Map.insert tgt found_info

-- -----------------------------------------------------------------------------
-- Refining an abstract state based upon a condition


-- See if expression matches form expected by jump tables
-- TODO: Fixme, this uses a fixed multiple of 8 for the jump table
matchJumpTable :: MemWidth (ArchAddrWidth arch)
               => Memory (ArchAddrWidth arch)
               -> BVValue arch ids (ArchAddrWidth arch) -- ^ Memory address that IP is read from.
               -> Maybe (ArchSegmentedAddr arch, BVValue arch ids (ArchAddrWidth arch))
matchJumpTable mem read_addr
    -- Turn the read address into base + offset.
  | Just (BVAdd _ offset base_val) <- valueAsApp read_addr
  , Just base <- asLiteralAddr mem base_val
    -- Turn the offset into a multiple by an index.
  , Just (BVMul _ (BVValue _ mul) jump_index) <- valueAsApp offset
  , mul == toInteger (addrSize (memAddrWidth mem))
  , Perm.isReadonly (segmentFlags (addrSegment base)) = do
    Just (base, jump_index)
matchJumpTable _ _ =
    Nothing

data JumpTableBoundsError arch ids
   = CouldNotInterpretAbsValue !(AbsValue (ArchAddrWidth arch) (BVType (ArchAddrWidth arch)))
   | UpperBoundMismatch !(Jmp.UpperBound (BVType (ArchAddrWidth arch))) !Integer
   | CouldNotFindBound String !(ArchAddrValue arch ids)

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

-- Returns the index bounds for a jump table of 'Nothing' if this is not a block
-- table.
getJumpTableBounds :: ( OrdF (ArchReg a)
                      , ShowF (ArchReg a)
                      , MemWidth (ArchAddrWidth a)
                      )
                   => ArchitectureInfo a
                   -> AbsProcessorState (ArchReg a) ids -- ^ Current processor registers.
                   -> ArchSegmentedAddr a -- ^ Base
                   -> BVValue a ids (ArchAddrWidth a) -- ^ Index in jump table
                   -> Either (JumpTableBoundsError a ids) (ArchAddr a)
                   -- ^ One past last index in jump table or nothing
getJumpTableBounds arch regs base jump_index =
  case transferValue regs jump_index of
    StridedInterval (SI.StridedInterval _ index_base index_range index_stride) -> do
      let index_end = index_base + (index_range + 1) * index_stride
      if rangeInReadonlySegment base (jumpTableEntrySize arch * fromInteger index_end) then
        case Jmp.unsignedUpperBound (regs^.indexBounds) jump_index of
          Right (Jmp.IntegerUpperBound bnd) | bnd == index_range -> Right $! fromInteger index_end
          Right bnd -> Left (UpperBoundMismatch bnd index_range)
          Left  msg -> Left (CouldNotFindBound  msg jump_index)
       else
        error $ "Jump table range is not in readonly memory"
--    TopV -> Left UpperBoundUndefined
    abs_value -> Left (CouldNotInterpretAbsValue abs_value)

tryLookupBlock :: String
               -> ArchSegmentedAddr arch
               -> Map Word64 (Block arch ids)
               -> ArchLabel arch
               -> Block arch ids
tryLookupBlock ctx base block_map lbl =
  if labelAddr lbl /= base then
    error $ "internal error: tryLookupBlock " ++ ctx ++ " given invalid addr " ++ show (labelAddr lbl)
  else
    case Map.lookup (labelIndex lbl) block_map of
      Nothing ->
        error $ "internal error: tryLookupBlock " ++ ctx ++ " " ++ show base
             ++ " given invalid index " ++ show (labelIndex lbl)
      Just b -> b

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

data ParseState arch ids = ParseState { _pblockMap :: !(Map Word64 (ParsedBlock arch ids))
                                        -- ^ Block m ap
                                      , _writtenCodeAddrs :: ![ArchSegmentedAddr arch]
                                        -- ^ Addresses marked executable that were written to memory.
                                      , _intraJumpTargets :: ![(ArchSegmentedAddr arch, AbsBlockState (ArchReg arch))]
                                      , _newFunctionAddrs :: ![ArchSegmentedAddr arch]
                                      }

pblockMap :: Simple Lens (ParseState arch ids) (Map Word64 (ParsedBlock arch ids))
pblockMap = lens _pblockMap (\s v -> s { _pblockMap = v })

writtenCodeAddrs :: Simple Lens (ParseState arch ids) [ArchSegmentedAddr arch]
writtenCodeAddrs = lens _writtenCodeAddrs (\s v -> s { _writtenCodeAddrs = v })

intraJumpTargets :: Simple Lens (ParseState arch ids) [(ArchSegmentedAddr arch, AbsBlockState (ArchReg arch))]
intraJumpTargets = lens _intraJumpTargets (\s v -> s { _intraJumpTargets = v })

newFunctionAddrs :: Simple Lens (ParseState arch ids) [ArchSegmentedAddr arch]
newFunctionAddrs = lens _newFunctionAddrs (\s v -> s { _newFunctionAddrs = v })


-- | Mark addresses written to memory that point to code as function entry points.
recordWriteStmt :: ( HasRepr (ArchReg arch) TypeRepr
                    , MemWidth (ArchAddrWidth arch)
                    , OrdF  (ArchReg arch)
                    , ShowF (ArchReg arch)
                    )
                 => ArchitectureInfo arch
                 -> Memory (ArchAddrWidth arch)
                 -> AbsProcessorState (ArchReg arch) ids
                 -> Stmt arch ids
                 -> State (ParseState arch ids) ()
recordWriteStmt arch_info mem regs stmt = do
  case stmt of
    WriteMem _addr repr v
      | Just Refl <- testEquality repr (addrMemRepr arch_info) -> do
          let addrs = concretizeAbsCodePointers mem (transferValue regs v)
          writtenCodeAddrs %= (addrs ++)
    _ -> return ()

-- | Attempt to identify the write to a stack return address, returning
-- instructions prior to that write and return  values.
--
-- This can also return Nothing if the call is not supported.
identifyCall :: ( RegConstraint (ArchReg a)
                , MemWidth (ArchAddrWidth a)
                )
             => Memory (ArchAddrWidth a)
             -> [Stmt a ids]
             -> RegState (ArchReg a) (Value a ids)
             -> Maybe (Seq (Stmt a ids), ArchSegmentedAddr a)
identifyCall mem stmts0 s = go (Seq.fromList stmts0) Seq.empty
  where -- Get value of stack pointer
        next_sp = s^.boundValue sp_reg
        -- Recurse on statements.
        go stmts after =
          case Seq.viewr stmts of
            Seq.EmptyR -> Nothing
            prev Seq.:> stmt
              -- Check for a call statement by determining if the last statement
              -- writes an executable address to the stack pointer.
              | WriteMem a _repr val <- stmt
              , Just _ <- testEquality a next_sp
                -- Check this is the right length.
              , Just Refl <- testEquality (typeRepr next_sp) (typeRepr val)
                -- Check if value is a valid literal address
              , Just val_a <- asLiteralAddr mem val
                -- Check if segment of address is marked as executable.
              , Perm.isExecutable (segmentFlags (addrSegment val_a)) ->
                Just (prev Seq.>< after, val_a)
                -- Stop if we hit any architecture specific instructions prior to
                -- identifying return address since they may have side effects.
              | ExecArchStmt _ <- stmt -> Nothing
                -- Otherwise skip over this instruction.
              | otherwise -> go prev (stmt Seq.<| after)

-- | This is designed to detect returns from the register state representation.
--
-- It pattern matches on a 'RegState' to detect if it read its instruction
-- pointer from an address that is 8 below the stack pointer.
--
-- Note that this assumes the stack decrements as values are pushed, so we will
-- need to fix this on other architectures.
identifyReturn :: RegConstraint (ArchReg arch)
               => RegState (ArchReg arch) (Value arch ids)
               -> Integer
                  -- ^ How stack pointer moves when a call is made
               -> Maybe (Assignment arch ids (BVType (ArchAddrWidth arch)))
identifyReturn s stack_adj = do
  let next_ip = s^.boundValue ip_reg
      next_sp = s^.boundValue sp_reg
  case next_ip of
    AssignedValue asgn@(Assignment _ (ReadMem ip_addr _))
      | let (ip_base, ip_off) = asBaseOffset ip_addr
      , let (sp_base, sp_off) = asBaseOffset next_sp
      , (ip_base, ip_off) == (sp_base, sp_off + stack_adj) -> Just asgn
    _ -> Nothing

data ParseContext arch ids = ParseContext { pctxMemory   :: !(Memory (ArchAddrWidth arch))
                                          , pctxArchInfo :: !(ArchitectureInfo arch)
                                          , pctxFunAddr  :: !(ArchSegmentedAddr arch)
                                            -- ^ Address of function this block is being parsed as
                                          , pctxAddr     :: !(ArchSegmentedAddr arch)
                                          , pctxBlockMap :: !(Map Word64 (Block arch ids))
                                          }

addrMemRepr :: ArchitectureInfo arch -> MemRepr (BVType (RegAddrWidth (ArchReg arch)))
addrMemRepr arch_info =
  case archAddrWidth arch_info of
    Addr32 -> BVMemRepr n4 (archEndianness arch_info)
    Addr64 -> BVMemRepr n8 (archEndianness arch_info)

-- | This parses a block that ended with a fetch and execute instruction.
parseFetchAndExecute :: forall arch ids
                     .  ArchConstraints arch
                     => ParseContext arch ids
                     -> ArchLabel arch
                     -> [Stmt arch ids]
                     -> AbsProcessorState (ArchReg arch) ids
                     -- ^ Registers at this block after statements executed
                     -> RegState (ArchReg arch) (Value arch ids)
                     -> State (ParseState arch ids) (ParsedBlock arch ids)
parseFetchAndExecute ctx lbl stmts regs s' = do
  let src = labelAddr lbl
  let lbl_idx = labelIndex lbl
  let mem = pctxMemory ctx
  let arch_info = pctxArchInfo ctx
  -- See if next statement appears to end with a call.
  -- We define calls as statements that end with a write that
  -- stores the pc to an address.
  let regs' = transferStmts arch_info regs stmts
  case () of
    -- The last statement was a call.
    -- Note that in some cases the call is known not to return, and thus
    -- this code will never jump to the return value.
    _ | Just (prev_stmts, ret) <- identifyCall mem stmts s' -> do
        Fold.mapM_ (recordWriteStmt arch_info mem regs') prev_stmts
        let abst = finalAbsBlockState regs' s'
        seq abst $ do
        -- Merge caller return information
        intraJumpTargets %= ((ret, archPostCallAbsState arch_info abst ret):)
        -- Look for new ips.
        let addrs = concretizeAbsCodePointers mem (abst^.absRegState^.curIP)
        newFunctionAddrs %= (++ addrs)
        pure ParsedBlock { pblockLabel = lbl_idx
                         , pblockStmts = Fold.toList prev_stmts
                         , pblockState = regs'
                         , pblockTerm  = ParsedCall s' (Just ret)
                         }

    -- This block ends with a return.
      | Just asgn' <- identifyReturn s' (callStackDelta arch_info) -> do

        let isRetLoad s =
              case s of
                AssignStmt asgn
                  | Just Refl <- testEquality (assignId asgn) (assignId  asgn') -> True
                _ -> False
            nonret_stmts = filter (not . isRetLoad) stmts

        mapM_ (recordWriteStmt arch_info mem regs') nonret_stmts

        let ip_val = s'^.boundValue ip_reg
        case transferValue regs' ip_val of
          ReturnAddr -> return ()
          -- The return_val is bad.
          -- This could indicate an imprecision in analysis or maybe unreachable/bad code.
          rv ->
            debug DCFG ("return_val is bad at " ++ show lbl ++ ": " ++ show rv) $
                  return ()
        pure ParsedBlock { pblockLabel = lbl_idx
                         , pblockStmts = nonret_stmts
                         , pblockState = regs'
                         , pblockTerm = ParsedReturn s'
                         }

      -- Jump to concrete offset.
      --
      -- Note, we disallow jumps back to function entry point thus forcing them to be treated
      -- as tail calls or unclassified if the stack has changed size.
      | Just tgt_addr <- asLiteralAddr mem (s'^.boundValue ip_reg)
      , tgt_addr /= pctxFunAddr ctx -> do
         assert (segmentFlags (addrSegment tgt_addr) `Perm.hasPerm` Perm.execute) $ do
         mapM_ (recordWriteStmt arch_info mem regs') stmts
         -- Merge block state and add intra jump target.
         let abst = finalAbsBlockState regs' s'
         let abst' = abst & setAbsIP tgt_addr
         intraJumpTargets %= ((tgt_addr, abst'):)
         pure ParsedBlock { pblockLabel = lbl_idx
                          , pblockStmts = stmts
                          , pblockState = regs'
                          , pblockTerm  = ParsedJump s' tgt_addr
                          }
      -- Block ends with what looks like a jump table.
      | AssignedValue (Assignment _ (ReadMem ptr _)) <- debug DCFG "try jump table" $ s'^.curIP
        -- Attempt to compute interval of addresses interval is over.
      , Just (base, jump_idx) <- matchJumpTable mem ptr ->
        case getJumpTableBounds arch_info regs' base jump_idx of
          Left err ->
            trace (show src ++ ": Could not compute bounds: " ++ showJumpTableBoundsError err) $ do
            mapM_ (recordWriteStmt arch_info mem regs') stmts
            pure ParsedBlock { pblockLabel = lbl_idx
                             , pblockStmts = stmts
                             , pblockState = regs'
                             , pblockTerm  = ClassifyFailure s'
                             }
          Right read_end -> do
            mapM_ (recordWriteStmt arch_info mem regs') stmts

            -- Try to compute jump table bounds

            let abst :: AbsBlockState (ArchReg arch)
                abst = finalAbsBlockState regs' s'
            seq abst $ do
            -- This function resolves jump table entries.
            -- It is a recursive function that has an index into the jump table.
            -- If the current index can be interpreted as a intra-procedural jump,
            -- then it will add that to the current procedure.
            -- This returns the last address read.
            let resolveJump :: [ArchSegmentedAddr arch]
                               -- /\ Addresses in jump table in reverse order
                            -> ArchAddr arch
                               -- /\ Current index
                            -> State (ParseState arch ids) [ArchSegmentedAddr arch]
                resolveJump prev idx | idx == read_end = do
                  -- Stop jump table when we have reached computed bounds.
                  return (reverse prev)
                resolveJump prev idx = do
                  let read_addr = base & addrOffset +~ 8 * idx
                  case readAddr mem (archEndianness arch_info) read_addr of
                      Right tgt_addr
                        | Perm.isReadonly (segmentFlags (addrSegment read_addr)) -> do
                          let flags = segmentFlags (addrSegment tgt_addr)
                          assert (flags `Perm.hasPerm` Perm.execute) $ do
                          let abst' = abst & setAbsIP tgt_addr
                          intraJumpTargets %= ((tgt_addr, abst'):)
                          resolveJump (tgt_addr:prev) (idx+1)
                      _ -> do
                        debug DCFG ("Stop jump table: " ++ show idx ++ " " ++ show read_end) $ do
                          return (reverse prev)
            read_addrs <- resolveJump [] 0
            pure ParsedBlock { pblockLabel = lbl_idx
                             , pblockStmts = stmts
                             , pblockState = regs'
                             , pblockTerm = ParsedLookupTable s' jump_idx (V.fromList read_addrs)
                             }

      -- Check for tail call (anything where we are right at stack height
      | ptrType    <- addrMemRepr arch_info
      , sp_val     <-  s'^.boundValue sp_reg
      , ReturnAddr <- transferReadMem regs' sp_val ptrType -> do

        mapM_ (recordWriteStmt arch_info mem regs') stmts

        -- Compute fina lstate
        let abst = finalAbsBlockState regs' s'
        seq abst $ do

        -- Look for new instruction pointers
        let addrs = concretizeAbsCodePointers mem (abst^.absRegState^.curIP)
        newFunctionAddrs %= (++ addrs)


        pure ParsedBlock { pblockLabel = lbl_idx
                         , pblockStmts = stmts
                         , pblockState = regs'
                         , pblockTerm  = ParsedCall s' Nothing
                         }

      -- Block that ends with some unknown
      | otherwise -> do
          trace ("Could not classify " ++ show lbl) $ do
          mapM_ (recordWriteStmt arch_info mem regs') stmts
          pure ParsedBlock { pblockLabel = lbl_idx
                           , pblockStmts = stmts
                           , pblockState = regs'
                           , pblockTerm  = ClassifyFailure s'
                           }

-- | This evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
parseBlocks :: ArchConstraints arch
            => ParseContext arch ids
               -- ^ Context for parsing blocks.
            -> [(Block arch ids, AbsProcessorState (ArchReg arch) ids)]
               -- ^ Queue of blocks to travese
            -> State (ParseState arch ids) ()
parseBlocks _ct [] = pure ()
parseBlocks ctx ((b,regs):rest) = do
  let mem       = pctxMemory ctx
  let arch_info = pctxArchInfo ctx
  let lbl = blockLabel b
  -- Assert we are still in source block.
  assert (pctxAddr ctx == labelAddr lbl) $ do
  let idx = labelIndex lbl
  let src = pctxAddr ctx
  let block_map = pctxBlockMap ctx
  -- FIXME: we should propagate c back to the initial block, not just b
  case blockTerm b of
    Branch c lb rb -> do
      let regs' = transferStmts arch_info regs (blockStmts b)
      mapM_ (recordWriteStmt arch_info mem regs') (blockStmts b)

      let l = tryLookupBlock "left branch"  src block_map lb
      let l_regs = refineProcStateBounds c True $ refineProcState c absTrue regs'
      let r = tryLookupBlock "right branch" src block_map rb
      let r_regs = refineProcStateBounds c False $ refineProcState c absFalse regs'
      -- We re-transfer the stmts to propagate any changes from
      -- the above refineProcState.  This could be more efficient by
      -- tracking what (if anything) changed.  We also might
      -- need to keep going back and forth until we reach a
      -- fixpoint
      let l_regs' = transferStmts arch_info l_regs (blockStmts b)
      let r_regs' = transferStmts arch_info r_regs (blockStmts b)


      let pb = ParsedBlock { pblockLabel = idx
                           , pblockStmts = blockStmts b
                           , pblockState = regs'
                           , pblockTerm  = ParsedBranch c (labelIndex lb) (labelIndex rb)
                           }
      pblockMap %= Map.insert idx pb

      parseBlocks ctx ((l, l_regs'):(r, r_regs'):rest)

    Syscall s' -> do
      let regs' = transferStmts arch_info regs (blockStmts b)
      mapM_ (recordWriteStmt arch_info mem regs') (blockStmts b)
      let abst = finalAbsBlockState regs' s'
      case concretizeAbsCodePointers mem (abst^.absRegState^.curIP) of
        [] -> error "Could not identify concrete system call address"
        [addr] -> do
          -- Merge system call result with possible next IPs.
          let post = archPostSyscallAbsState arch_info abst addr

          intraJumpTargets %= ((addr, post):)
          let pb = ParsedBlock { pblockLabel = idx
                               , pblockStmts = blockStmts b
                               , pblockState = regs'
                               , pblockTerm  = ParsedSyscall s' addr
                               }
          pblockMap %= Map.insert idx pb
          parseBlocks ctx rest
        _ -> error "Multiple system call addresses."


    FetchAndExecute s' -> do
      pb <- parseFetchAndExecute ctx (blockLabel b) (blockStmts b) regs s'
      pblockMap %= Map.insert idx pb
      parseBlocks ctx rest

    -- Do nothing when this block ends in a translation error.
    TranslateError _ msg -> do
      let regs' = transferStmts arch_info regs (blockStmts b)
      let pb = ParsedBlock { pblockLabel = idx
                           , pblockStmts = blockStmts b
                           , pblockState = regs'
                           , pblockTerm = ParsedTranslateError msg
                           }
      pblockMap %= Map.insert idx pb
      parseBlocks ctx rest


-- | This evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
transferBlocks :: ArchConstraints arch
               => BlockRegion arch ids
               -- ^ Input block regions
               -> AbsProcessorState (ArchReg arch) ids
               -- ^ Abstract state describing machine state when block is encountered.
              -> FunM arch ids ()
transferBlocks br regs =
  case Map.lookup 0 (brBlocks br) of
    Nothing -> do
      error $ "transferBlocks given empty blockRegion."
    Just b -> do
      funAddr <- gets curFunAddr
      s <- liftCFG get
      let src = labelAddr (blockLabel b)
      let ctx = ParseContext { pctxMemory   = memory s
                             , pctxArchInfo = archInfo s
                             , pctxFunAddr  = funAddr
                             , pctxAddr     = src
                             , pctxBlockMap = brBlocks br
                             }
      let ps0 = ParseState { _pblockMap = Map.empty
                           , _writtenCodeAddrs = []
                           , _intraJumpTargets = []
                           , _newFunctionAddrs = []
                           }
      let ps = execState (parseBlocks ctx [(b,regs)]) ps0
      let pb = ParsedBlockRegion { regionAddr = src
                                 , regionSize = brSize br
                                 , regionBlockMap = ps^.pblockMap
                                 }
      curFunInfo . parsedBlocks %= Map.insert src pb
      liftCFG $ mapM_ (markAddrAsFunction (InWrite src)) (ps^.writtenCodeAddrs)
      liftCFG $ mapM_ (markAddrAsFunction (CallTarget src)) (ps^.newFunctionAddrs)
      mapM_ (\(addr, abs_state) -> mergeIntraJump src abs_state addr) (ps^.intraJumpTargets)

transfer :: ArchConstraints arch
         => ArchSegmentedAddr arch
         -> FunM arch ids ()
transfer addr = do
  mfinfo <- use $ curFunInfo . foundAddrs . at addr
  case mfinfo of
    Nothing -> error $ "getBlock called on unfound address " ++ show addr ++ "."
    Just finfo -> do
      info      <- liftCFG $ gets archInfo
      nonce_gen <- liftCFG $ gets nonceGen
      mem       <- liftCFG $ gets memory
      -- Attempt to disassemble block.
      -- Get memory so that we can decode from it.
      -- Returns true if we are not at the start of a block.
      -- This is used to stop the disassembler when we reach code
      -- that is part of a new block.
      prev_block_map <- use $ curFunInfo . parsedBlocks
      let not_at_block = (`Map.notMember` prev_block_map)
      let ab = foundAbstractState finfo
      (bs, next_ip, maybeError) <- liftCFG $ liftST $ disassembleFn info nonce_gen mem not_at_block addr ab
      -- Build state for exploring this.
      case maybeError of
        Just e -> do
          trace ("Failed to disassemble " ++ show e) $ pure ()
        Nothing -> do
          pure ()

      assert (segmentIndex (addrSegment next_ip) == segmentIndex (addrSegment addr)) $ do
      assert (next_ip^.addrOffset > addr^.addrOffset) $ do
      let block_map = Map.fromList [ (labelIndex (blockLabel b), b) | b <- bs ]
      let br = BlockRegion { brSize = next_ip^.addrOffset - addr^.addrOffset
                           , brBlocks = block_map
                           }
      transferBlocks br $ initAbsProcessorState mem (foundAbstractState finfo)

------------------------------------------------------------------------
-- Main loop

-- | Explore a specific function
explore_fun_loop :: ArchConstraints arch => FunM arch ids ()
explore_fun_loop = do
  st <- FunM get
  case Set.minView (st^.frontier) of
    Nothing -> return ()
    Just (addr, next_roots) -> do
      FunM $ put $ st & frontier .~ next_roots
      transfer addr
      explore_fun_loop

explore_fun :: ArchConstraints arch
            => ArchSegmentedAddr arch
            -> CodeAddrReason (ArchAddrWidth arch)
            -> CFGM arch ids ()
explore_fun addr rsn = do
  s <- get
  let info = archInfo s
  let mem  = memory s

  let initFunInfo = initDiscoveryFunInfo info mem (symbolNames s) addr rsn
  let fs0 = FunState { curFunAddr = addr
                     , _curFunInfo = initFunInfo
                     , _frontier = Set.singleton addr
                     }
  fs <- execStateT (unFunM explore_fun_loop) fs0
  funInfo %= Map.insert addr (fs^.curFunInfo)

explore_frontier :: ArchConstraints arch
                 => CFGM arch ids ()
explore_frontier = do
  st <- get
  -- If local block frontier is empty, then try function frontier.
  case Map.minViewWithKey (st^.function_frontier) of
    Nothing -> return ()
    Just ((addr, rsn), next_roots) -> do
      put $! st & function_frontier .~ next_roots
      explore_fun addr rsn
      explore_frontier

-- | This returns true if the address is writable and value, and points to code.
memIsDataCodePointer :: Memory w -> SegmentedAddr w -> SegmentedAddr w -> Bool
memIsDataCodePointer _ a v
  =  segmentFlags (addrSegment v) `Perm.hasPerm` Perm.execute
  && segmentFlags (addrSegment a) `Perm.hasPerm` Perm.write

-- | Map from addresses to the associated symbol name.
type SymbolNameMap w = Map (SegmentedAddr w) BSC.ByteString


-- | This checks the symbol name map for correctness of the symbol names.
--
-- It returns either an error message or (Right ()) if no error is found.
checkSymbolMap :: SymbolNameMap w -> Either String ()
checkSymbolMap symbols
  | (Set.size symbol_names /= Map.size symbols)
  , debug DCFG ("WARNING: The symbol name map contains duplicate symbol names") False
  = error "internal: duplicate symbol names in symbol name map"
  where symbol_names :: Set BSC.ByteString
        symbol_names = Set.fromList (Map.elems symbols)
checkSymbolMap symbols = do
  forM_ (Map.elems symbols) $ \sym_nm -> do
    case BSC.unpack sym_nm of
      [] -> Left "Empty symbol name"
      (c:_) | isDigit c -> Left "Symbol name that starts with a digit."
            | otherwise -> Right ()

-- | Construct a discovery info by starting with exploring from a given set of
-- function entry points.
cfgFromAddrs :: forall arch
             .  ArchConstraints arch
             => ArchitectureInfo arch
                -- ^ Architecture-specific information needed for doing control-flow exploration.
             -> Memory (ArchAddrWidth arch)
                -- ^ Memory to use when decoding instructions.
             -> SymbolNameMap (ArchAddrWidth arch)
                -- ^ Map from addresses to the associated symbol name.
             -> [ArchSegmentedAddr arch]
                -- ^ Initial function entry points.
             -> [(ArchSegmentedAddr arch, ArchSegmentedAddr arch)]
                -- ^ Function entry points in memory to be explored
                -- after exploring function entry points.
                --
                -- Each entry contains an address and the value stored in it.
             -> Some (DiscoveryInfo arch)
cfgFromAddrs arch_info mem symbols init_addrs mem_words =
  runCFGM arch_info mem symbols $ do
    case checkSymbolMap symbols of
      Left msg -> error $ "interna error in cfgFromAddrs:" ++ msg
      Right () -> pure ()
    -- Set abstract state for initial functions
    mapM_ (markAddrAsFunction InitAddr) init_addrs
    explore_frontier
    -- Add in code pointers from memory.
    let notAlreadyFunction s _a v = not (Set.member v (s^.functionEntries))
    s <- get
    let mem_addrs =
          filter (uncurry (notAlreadyFunction s)) $
          filter (uncurry (memIsDataCodePointer mem)) $
          mem_words
    mapM_ (\(src,val) -> markAddrAsFunction (CodePointerInMem src) val) mem_addrs
    explore_frontier
