{-| This performs a whole-program analysis to compute which registers
are needed to evaluate different blocks.  It can be used to compute
which registers are needed for function arguments.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.Analysis.FunctionArgs
  ( functionDemands
    -- * Callbacks for architecture-specific information
  , ArchDemandInfo(..)
  , ArchTermStmtRegEffects(..)
  , ComputeArchTermStmtEffects
  , ResolveCallArgsFn
    -- * Demands
  , AddrDemandMap
  , DemandSet(..)
    -- * Errors
  , FunctionSummaryFailureMap
  , FunctionArgAnalysisFailure(..)
    -- * Utilities
  , RegSegmentOff
  , RegisterSet
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Foldable
import qualified Data.Kind as Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe

import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
  ( DemandContext
  , demandConstraints
  , hasSideEffects
  )
import           Data.Macaw.Discovery.State
import           Data.Macaw.Types

-------------------------------------------------------------------------------
--PreBlockMap

-- | Map from blocks to their predcessors within a function.
type PredBlockMap arch = Map (ArchSegmentOff arch) [ArchSegmentOff arch]

-- | Generate map from block within a function to their predecessors
predBlockMap :: DiscoveryFunInfo arch ids -> PredBlockMap arch
predBlockMap finfo =
  Map.fromListWith (++)
    [ (dest, [pblockAddr b])
    | b <- Map.elems (finfo^.parsedBlocks)
    , dest <- parsedTermSucc (pblockTermStmt b)
    ]

-------------------------------------------------------------------------------

-- The algorithm computes the set of direct deps (i.e., from writes)
-- and then iterates, propagating back via the register deps.  It
-- doesn't compute assignment uses (although it could) mainly to keep
-- memory use down.  We recompute assignment use later in RegisterUse.
--
-- The basic question this analysis answers is: what arguments does a
-- function require, and what results does it produce?
--
-- There are 3 phases
-- 1. Block-local summarization
-- 2. Function-local summarization
-- 3. Global fixpoint calculation.
--
-- The first 2 phases calculate, for each function, the following information:
--
-- A. What registers are required by a function (ignoring function
--    calls)?
--
-- B. Given that result register {rax, rdx, xmm0} is demanded, what
--    extra register arguments are required, and what extra result
--    arguments are required?
--
-- C. Given that function f now requires argument r, what extra
--    arguments are required, and what extra result registers are
--    demanded?

-- | A set of registers
type RegisterSet (r :: Type -> Kind.Type) = Set (Some r)

-- | A memory segment offset compatible with the architecture registers.
type RegSegmentOff r = MemSegmentOff (RegAddrWidth r)

-- | This stores the information that is needed to compute a value of some sort.
data DemandSet (r :: Type -> Kind.Type) =
    DemandSet { registerDemands       :: !(RegisterSet r)
                -- | Maps a function address to the registers we need it to return.
              , functionResultDemands :: !(Map (MemSegmentOff (RegAddrWidth r)) (RegisterSet r))
              }

-- | Return True if the demand set indicates no registers are needed.
isEmptyDemandSet :: DemandSet r -> Bool
isEmptyDemandSet ds =
  Set.null (registerDemands ds) && Map.null (functionResultDemands ds)

-- | Create a demand set for specific registers.
registerDemandSet :: RegisterSet r -> DemandSet r
registerDemandSet s = DemandSet { registerDemands = s
                                , functionResultDemands = Map.empty
                                }

-- | @demandFunctionReturn f r@ demands the return register of @r@ from @f@.
demandFunctionReturn :: MemSegmentOff (RegAddrWidth r) -> Some r -> DemandSet r
demandFunctionReturn faddr sr =
  DemandSet { registerDemands = Set.empty
            , functionResultDemands = Map.singleton faddr (Set.singleton sr)
            }

deriving instance (ShowF r, MemWidth (RegAddrWidth r)) => Show (DemandSet r)
deriving instance TestEquality r => Eq (DemandSet r)
deriving instance OrdF r => Ord (DemandSet r)

instance OrdF r => Semigroup (DemandSet r) where
  ds1 <> ds2 =
    DemandSet { registerDemands = registerDemands ds1 <> registerDemands ds2
              , functionResultDemands =
                  Map.unionWith Set.union (functionResultDemands ds1)
                                          (functionResultDemands ds2)
              }

instance OrdF r => Monoid (DemandSet r) where
  mempty = DemandSet { registerDemands = Set.empty
                     , functionResultDemands = Map.empty
                     }

demandSetDifference :: OrdF r => DemandSet r -> DemandSet r -> DemandSet r
demandSetDifference ds1 ds2 =
  DemandSet { registerDemands = registerDemands ds1 `Set.difference` registerDemands ds2
            , functionResultDemands =
                Map.differenceWith setDiff
                (functionResultDemands ds1)
                (functionResultDemands ds2)
            }
  where
    setDiff s1 s2 =
      let s' = s1 `Set.difference` s2
      in if Set.null s' then Nothing else Just s'

-- | This type is used to describe the context in which a particular
-- demand set is needed.
data DemandType r
  -- | This denotes demands that are always neede to execute the block.
  = DemandAlways
  -- | This denotes a value needed if the function at the given
  -- address needs the specific register as an argument.
  | forall tp. DemandFunctionArg (RegSegmentOff r) (r tp)
    -- | This key is used to denote the demands associating with
    -- needing to compute the the return value of the
    -- function stored in the given register.
  | forall tp. DemandFunctionResult (r tp)

instance (MemWidth (RegAddrWidth r), ShowF r) => Show (DemandType r) where
  showsPrec _ DemandAlways  = showString "DemandAlways"
  showsPrec p (DemandFunctionArg a r) = showParen (p >= 10) $
    showString "DemandFunctionArg " . shows a . showChar ' ' . showsF r
  showsPrec p (DemandFunctionResult r) = showParen (p >= 10) $
    showString "DemandFunctionResult " . showsF r

instance TestEquality r => Eq (DemandType r) where
  DemandAlways == DemandAlways = True
  (DemandFunctionArg faddr1 r1) == (DemandFunctionArg faddr2 r2) =
    faddr1 == faddr2 && isJust (testEquality r1 r2)
  (DemandFunctionResult r1) == (DemandFunctionResult r2) =
    isJust (testEquality r1 r2)
  _ == _ = False

instance OrdF r => Ord (DemandType r) where
  DemandAlways `compare` DemandAlways = EQ
  DemandAlways `compare` _  = LT
  _ `compare` DemandAlways  = GT

  (DemandFunctionArg faddr1 r1) `compare` (DemandFunctionArg faddr2 r2)
    | faddr1 == faddr2 = toOrdering (compareF r1 r2)
    | otherwise = faddr1 `compare` faddr2

  (DemandFunctionArg {}) `compare` _ = LT
  _ `compare` (DemandFunctionArg {}) = GT

  (DemandFunctionResult r1) `compare` (DemandFunctionResult r2) =
    toOrdering (compareF r1 r2)

-- | This maps information produced by the block to what is needed to
-- produce that information.
newtype BlockDemands r = BD (Map (DemandType r) (DemandSet r))

demandAlways :: DemandSet r -> BlockDemands r
demandAlways s = BD (Map.singleton DemandAlways s)

-- | Record requirements to compute the value of an argument to a
-- function at the given address (if the function turns out to need
-- that register).
addDemandFunctionArg :: OrdF r
                     => RegSegmentOff r  -- ^ Register with demands.
                     -> r tp        -- ^ Register for this argument
                     -> DemandSet r -- ^ Demands for argument
                     -> BlockDemands r -- ^ Current known demands for block.
                     -> BlockDemands r
addDemandFunctionArg a r s (BD m) = BD (Map.insertWith mappend (DemandFunctionArg a r) s m)

-- | Record requirements to compute the return value of the given function.
addDemandFunctionResult :: OrdF r => r tp -> DemandSet r -> BlockDemands r -> BlockDemands r
addDemandFunctionResult r s (BD m) = BD (Map.insertWith mappend (DemandFunctionResult r) s m)

-- | Take the union of the demands.
unionBlockDemands :: OrdF r => BlockDemands r -> BlockDemands r -> BlockDemands r
unionBlockDemands (BD x) (BD y) = BD (Map.unionWith mappend x y)

instance OrdF r => Semigroup (BlockDemands r) where
  (<>) = unionBlockDemands

instance OrdF r => Monoid (BlockDemands r) where
  mempty = BD Map.empty

-- | A cache from assignment identifiers to registers.
type AssignmentCache r ids = Map (Some (AssignId ids)) (RegisterSet r)

-- | Maps each register to the what information is needed to compute
-- the value stored in that register.
--
-- To reduce the size of the underlying map, this does not including
-- bindings for registers that need no additional information to be
-- computed.
newtype FinalRegisterDemands r = FRD (Map (Some r) (DemandSet r))

-- | Add demands for a register to collection.
insertRegDemand :: OrdF r
                => r tp
                -> DemandSet r
                -> FinalRegisterDemands r
                -> FinalRegisterDemands r
insertRegDemand r s (FRD m)
  | isEmptyDemandSet s = FRD m
  | otherwise = FRD (Map.insertWith mappend (Some r) s m)

-- | @postRegisterDemands s r@ returns the demand set needed to
-- compute @r@ in @s@.
postRegisterDemands :: OrdF r => FinalRegisterDemands r -> r tp -> DemandSet r
postRegisterDemands (FRD m) r = m^.ix (Some r)

instance OrdF r => Semigroup (FinalRegisterDemands r) where
  FRD x <> FRD y = FRD (Map.unionWith mappend x y)

instance OrdF r => Monoid (FinalRegisterDemands r) where
  mempty = FRD Map.empty

-- | Describes the effects of an architecture-specific statement
data ArchTermStmtRegEffects arch
   = ArchTermStmtRegEffects { termRegDemands :: ![Some (ArchReg arch)]
                              -- ^ Registers demanded by term statement
                            , termRegTransfers :: ![Some (ArchReg arch)]
                              -- ^ Registers that are not modified by
                              -- terminal statement.
                            }

-- | Returns information about the registers needed and modified by a
-- terminal statement
--
-- The first argument is the terminal statement.
--
-- The second is the state of registers when it is executed.
type ComputeArchTermStmtEffects arch ids
   = ArchTermStmt arch ids
   -> RegState (ArchReg arch) (Value arch ids)
   -> ArchTermStmtRegEffects arch

-- | Information about the architecture/environment what arguments a
-- function needs.
data ArchDemandInfo arch = ArchDemandInfo
     { -- | Registers the ABI says a function may use for its arguments.
       functionArgRegs :: ![Some (ArchReg arch)]
       -- | Registers the ABI says a function may use to return values.
     , functionRetRegs :: ![Some (ArchReg arch)]
       -- | Registers the ABI specifies that callees should save.
     , calleeSavedRegs :: !(Set (Some (ArchReg arch)))
       -- | Compute the effects of a terminal statement on registers.
     , computeArchTermStmtEffects :: !(forall ids . ComputeArchTermStmtEffects arch ids)
       -- | Information needed to infer what values are demanded by a AssignRhs and Stmt.
     , demandInfoCtx :: !(DemandContext arch)
     }

------------------------------------------------------------------------
-- FunArgContext

-- | Function for resolving arguments to call.
--
-- Takes address if callsite and registers.
type ResolveCallArgsFn arch
  = forall ids
  .  MemSegmentOff (ArchAddrWidth arch)
  -> RegState (ArchReg arch) (Value arch ids)
  -> Either String [Some (Value arch ids)]

-- | Contextual information to inform argument computation.
data FunArgContext arch = FAC
  { archDemandInfo :: !(ArchDemandInfo arch)
  , ctxMemory :: !(Memory (ArchAddrWidth arch))
    -- ^ State of memory for code analysis
  , computedAddrSet :: !(Set (ArchSegmentOff arch))
    -- ^ Set of addresses that we are current computing addresses for.
  , resolveCallArgs :: !(ResolveCallArgsFn arch)
    -- ^ Given a call with the registers, this infers the arguments
    -- returned by the call or an error message if it cannot be inferred.
  }

-- | This is information needed to compute dependencies for a single function.
data FunctionArgsState arch ids = FAS
  { -- | If a demand d is demanded of block address then the block
    --   demands S, s.t.  `blockDemandMap ^. at addr ^. at d = Just S1
    _blockDemandMap    :: !(Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch)))
    -- | A cache of the assignments and their deps.  The key is not
    -- included in the set of deps (but probably should be).
  , _assignmentCache :: !(AssignmentCache (ArchReg arch) ids)
  }

blockDemandMap :: Simple Lens (FunctionArgsState arch ids)
                    (Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch)))
blockDemandMap = lens _blockDemandMap (\s v -> s { _blockDemandMap = v })

assignmentCache :: Simple Lens (FunctionArgsState arch ids) (AssignmentCache (ArchReg arch) ids)
assignmentCache = lens _assignmentCache (\s v -> s { _assignmentCache = v })

initFunctionArgsState :: FunctionArgsState arch ids
initFunctionArgsState =
  FAS { _blockDemandMap    = Map.empty
      , _assignmentCache   = Map.empty
      }

-- | Describes a reason a function call failed.
data FunctionArgAnalysisFailure w
   = CallAnalysisError !(MemSegmentOff w) !String
     -- ^ Could not determine call arguments.
   | PLTStubNotSupported
     -- ^ PLT stub analysis not supported.

-- | Monad that runs for computing the dependcies of each block.
type FunctionArgsM arch ids =
  StateT (FunctionArgsState arch ids)
         (ReaderT (FunArgContext arch) (Except (FunctionArgAnalysisFailure (ArchAddrWidth arch))))

evalFunctionArgsM :: FunArgContext arch
                  -> FunctionSummaries (ArchReg arch) -- ^ Existing summaries
                  -> ArchSegmentOff arch -- ^ Address of function we are initializing
                  -> FunctionArgsM arch ids (FunctionSummaries (ArchReg arch))
                  -> FunctionSummaries (ArchReg arch)
evalFunctionArgsM ctx s faddr m =
  case runExcept (runReaderT (evalStateT m initFunctionArgsState) ctx) of
    Left e -> s { inferenceFails = Map.insert faddr e (inferenceFails s) }
    Right r' -> r'

-- ----------------------------------------------------------------------------------------
-- Phase one functions

withAssignmentCache :: State (AssignmentCache (ArchReg arch) ids)  a -> FunctionArgsM arch ids a
withAssignmentCache m = do
  c <- use assignmentCache
  let (r, c') = runState m c
  seq c' $ assignmentCache .= c'
  pure r

-- | Return the input registers that a value depends on.
--
-- Note. This caches the assignment register sets so that we do not
-- need to recalculate the demand set for assignments referenced
-- multiple times.
valueUses :: (OrdF (ArchReg arch), FoldableFC (ArchFn arch))
          => Value arch ids tp
          -> State (AssignmentCache (ArchReg arch) ids) (RegisterSet (ArchReg arch))
valueUses (AssignedValue (Assignment a rhs)) = do
   mr <- gets $ Map.lookup (Some a)
   case mr of
     Just s -> pure s
     Nothing -> do
       rhs' <- foldlMFC (\s v -> seq s $ Set.union s <$> valueUses v) Set.empty rhs
       seq rhs' $ modify' $ Map.insert (Some a) rhs'
       pure $ rhs'
valueUses (Initial r) =
  pure $! Set.singleton (Some r)
valueUses _ =
  pure $! Set.empty

addValueUses :: (OrdF (ArchReg arch), FoldableFC (ArchFn arch))
             => RegisterSet (ArchReg arch)
             -> Value arch ids tp
             -> State (AssignmentCache (ArchReg arch) ids) (RegisterSet (ArchReg arch))
addValueUses s v = Set.union s <$> valueUses v

addBlockDemands :: OrdF (ArchReg arch)
                => ArchSegmentOff arch
                -> BlockDemands (ArchReg arch)
                -> FunctionArgsM arch ids ()
addBlockDemands a m =
  blockDemandMap %= Map.insertWith unionBlockDemands a m

-- | Given a block and a maping from register to value after the block
-- has executed, this traverses the registers that will be available
-- in future blocks, and records a mapping from those registers to
-- their input dependencies.
recordBlockTransfer :: forall arch ids t
                    .  ( RegisterInfo (ArchReg arch)
                       , FoldableFC (ArchFn arch)
                       , Foldable t
                       )
                    => ArchSegmentOff arch
                       -- ^ Address of current block.
                    -> RegState (ArchReg arch) (Value arch ids)
                       -- ^ Map from registers to values.
                    -> t (Some (ArchReg arch))
                       -- ^ List of registers that subsequent blocks may depend on.
                    -> FunctionArgsM arch ids (FinalRegisterDemands (ArchReg arch))
recordBlockTransfer _addr regs regSet = do
  let doReg :: FinalRegisterDemands (ArchReg arch)
            -> Some (ArchReg arch)
            -> State (AssignmentCache (ArchReg arch) ids)
                     (FinalRegisterDemands (ArchReg arch))
      doReg m (Some r) =
        case testEquality r ip_reg of
          Just _ -> pure m
          Nothing -> do
            rs' <- valueUses (regs^.boundValue r)
            pure $! insertRegDemand r (registerDemandSet rs') m
  withAssignmentCache $ foldlM doReg mempty regSet

-- | A block requires a value, and so we need to remember which
-- registers are required.
demandValue :: (OrdF (ArchReg arch), FoldableFC (ArchFn arch))
            => ArchSegmentOff arch
            -> Value arch ids tp
            -> FunctionArgsM arch ids ()
demandValue addr v = do
  regs <- withAssignmentCache $ valueUses v
  addBlockDemands addr $ demandAlways (registerDemandSet regs)

-- -----------------------------------------------------------------------------
-- Entry point

-- | Maps each function to the demand set for that function.
type AddrDemandMap r = Map (RegSegmentOff r) (DemandSet r)

-- | Maps a pair of (addr,reg) to the additional demands needed if the
-- function at @addr@ needs @reg@ as an argument.
type ArgDemandsMap r = Map (RegSegmentOff r, Some r) (AddrDemandMap r)

-- | This updates the demand information to demand the values in
-- certain registers when a call to a function we are inferring
-- demands the value.
linkKnownCallArguments :: ( FoldableFC (ArchFn arch)
                          , RegisterInfo (ArchReg arch)
                          )
                       => BlockDemands (ArchReg arch)
                       -> ArchSegmentOff arch
                          -- ^ Address of function we are calling
                       -> RegState (ArchReg arch) (Value arch ids)
                          -- ^ The mapping registers to values when the call occurs.
                       -> FunctionArgsM arch ids (BlockDemands (ArchReg arch))
linkKnownCallArguments curBlockDemands faddr regs = do
  -- Associate the demand sets for each potential argument
  -- register with the registers used by faddr.
  argRegs <- asks $ functionArgRegs . archDemandInfo
  -- Get current demands associated with block.
  let insertArgRegDemands m (Some r) = do
        vals <- valueUses (regs^. boundValue r)
        pure $! addDemandFunctionArg faddr r (registerDemandSet vals) m
  -- Add demands for computing an argument register value.
  withAssignmentCache $ foldlM insertArgRegDemands curBlockDemands argRegs

-- | This updates the block demand and transfer information to connect
-- demand for registers after the call to the information we expect
-- the call to return.
--
-- Its primary pupose is to add the glue that tells a caller when
-- its caller reads its return information.
linkKnownCallReturnValues :: forall arch ids
                          . ( RegisterInfo (ArchReg arch)
                            , FoldableFC (ArchFn arch)
                            )
                          => ArchSegmentOff arch
                             -- ^ Address of this block
                          -> ArchSegmentOff arch
                             -- ^ Address of function we are calling
                          -> RegState (ArchReg arch) (Value arch ids)
                          -- ^ The mapping registers to values when the call occurs.
                          -> Maybe (ArchSegmentOff arch)
                             -- ^ Address to return to or `Nothing` for tail call.
                          -> FunctionArgsM arch ids (FinalRegisterDemands (ArchReg arch))
linkKnownCallReturnValues blockAddr faddr regs mReturnAddr = do
  ainfo <- asks archDemandInfo

  let retRegs = functionRetRegs ainfo

  case mReturnAddr of
    Nothing -> do
      -- Get demands for this block.
      curDemandMap <- Map.findWithDefault mempty blockAddr <$> use blockDemandMap

      -- For each return register @r@, extend @curDemandMap@ so that
      -- to indicate that if a caller demands this function returns
      -- register @r@, then it is demanded that @faddr@ returns
      -- register @r@.
      let addRetRegDemands m (Some r) =
            addDemandFunctionResult r (demandFunctionReturn faddr (Some r)) m
      let nextDemandMap = foldl' addRetRegDemands curDemandMap retRegs
      -- Update new demands for address.
      blockDemandMap %= Map.insert blockAddr nextDemandMap
      -- Do not worry about registers provided if function does not return.
      pure mempty
    Just _ -> do

      -- Compute final register demands for registers preserved by calls, and return registers.
      newDemands <-
        recordBlockTransfer blockAddr regs (Some sp_reg : Set.toList (calleeSavedRegs ainfo))

      -- return registers that demanding the register
      let linkRetReg m (Some r) = insertRegDemand r (demandFunctionReturn faddr (Some r)) m

      let srDemandSet :: FinalRegisterDemands (ArchReg arch)
          srDemandSet = foldl linkRetReg newDemands retRegs
      pure srDemandSet

-- | This records information about a call from the given block to the
-- target block.
summarizeCall :: forall arch ids
              .  ( FoldableFC (ArchFn arch)
                 , RegisterInfo (ArchReg arch)
                 )
              => ArchSegmentOff arch
                 -- ^ The label for the current block.
              -> ArchAddrWord arch
                 -- ^ Offset from start of block for the call instruction.
              -> RegState (ArchReg arch) (Value arch ids)
                 -- ^ The current mapping from registers to values
              -> Maybe (ArchSegmentOff arch)
                 -- ^ Address to return to or `Nothing` for tail call.
              -> FunctionArgsM arch ids (FinalRegisterDemands (ArchReg arch))
summarizeCall blockAddr callOff finalRegs mReturnAddr = do
  ctx <- ask

  let ipVal = finalRegs^.boundValue ip_reg
  let spVal = finalRegs^.boundValue sp_reg

  -- Record stack pointer and IP is always needed.
  do demands <- withAssignmentCache $ foldlM addValueUses Set.empty [ipVal, spVal]
     addBlockDemands blockAddr $ demandAlways (registerDemandSet demands)


  case () of
    -- When we call a function whose arguments we are concurrently
    -- trying to compute, we need to link the fact that if the
    -- function demands a register then we demand the register.
    _ | Just faddr <- valueAsSegmentOff (ctxMemory ctx) ipVal
      , Set.member faddr (computedAddrSet ctx) -> do

      curBlockDemands <- Map.findWithDefault mempty blockAddr <$> use blockDemandMap
      newBlockDemands <- linkKnownCallArguments curBlockDemands faddr finalRegs
      -- Update new demands for address.
      blockDemandMap %= Map.insert blockAddr newBlockDemands
      linkKnownCallReturnValues blockAddr faddr finalRegs mReturnAddr

    -- Otherwise we compute statically what information to record.
    _ -> do

      let ainfo = archDemandInfo ctx

      let callAddr =
            case incSegmentOff blockAddr (toInteger callOff) of
              Just a -> a
              Nothing -> error "Call site is not a valid address."
      argValues <-
        case resolveCallArgs ctx callAddr finalRegs of
          Left e -> throwError (CallAnalysisError callAddr e)
          Right r -> pure r
      let regUses s (Some v) = addValueUses s v
      demands <- withAssignmentCache $ foldlM regUses Set.empty argValues
      addBlockDemands blockAddr $ demandAlways (registerDemandSet demands)

      -- Only need registers if this call has a return value.
      if isJust mReturnAddr then do
        -- Copy callee saved registers and stack pointer across function.
        let savedRegs = Some sp_reg : Set.toList (calleeSavedRegs ainfo)
        recordBlockTransfer blockAddr finalRegs savedRegs
       else
        pure mempty

recordStmtsDemands :: OrdF (ArchReg arch)
                   => MemSegmentOff (ArchAddrWidth arch) -- ^ Address of block
                   -> ArchAddrWord arch -- ^ Offset from start of block of current instruction.
                   -> [Stmt arch ids]
                   -> FunctionArgsM arch ids (ArchAddrWord arch)
recordStmtsDemands _blockAddr off [] = do
  pure off
recordStmtsDemands blockAddr off (stmt:stmts) = do
  ctx <- asks $ demandInfoCtx . archDemandInfo
  demandConstraints ctx $ do
   case stmt of
    AssignStmt a -> do
      when (hasSideEffects ctx (assignRhs a)) $ do
        traverseFC_ (demandValue blockAddr) (assignRhs a)
      recordStmtsDemands blockAddr off stmts
    WriteMem addr _ v -> do
      demandValue blockAddr addr
      demandValue blockAddr v
      recordStmtsDemands blockAddr off stmts
    CondWriteMem cond addr _ v -> do
      demandValue blockAddr cond
      demandValue blockAddr addr
      demandValue blockAddr v
      recordStmtsDemands blockAddr off stmts
    InstructionStart off' _ -> do
      recordStmtsDemands blockAddr off' stmts
    Comment _ -> do
      recordStmtsDemands blockAddr off stmts
    ExecArchStmt astmt -> do
      traverseF_ (demandValue blockAddr) astmt
      recordStmtsDemands blockAddr off stmts
    ArchState _addr _assn -> do
      recordStmtsDemands blockAddr off stmts

-- | This function figures out what the block requires
-- (i.e., addresses that are stored to, and the value stored), along
-- with a map of how demands by successor blocks map back to
-- assignments and registers.
summarizeBlock :: forall arch ids
               .  ArchConstraints arch
               => ParsedBlock arch ids -- ^ Current block
               -> FunctionArgsM arch ids (FinalRegisterDemands (ArchReg arch))
summarizeBlock b = do
  let blockAddr = pblockAddr b

  -- Add this label to block demand map with empty set.
  addBlockDemands blockAddr mempty

  ctx <- ask
  let ainfo = archDemandInfo ctx
  -- Add all values demanded by non-terminal statements in list.
  finalOff <- recordStmtsDemands blockAddr 0 (pblockStmts b)
  -- Add values demanded by terminal statements
  case pblockTermStmt b of
    ParsedCall regs mRetAddr -> do
      -- Record the demands based on the call, and add edges between
      -- this note and next nodes.
      summarizeCall blockAddr finalOff regs mRetAddr

    PLTStub{} -> do
      throwError PLTStubNotSupported
    ParsedJump regs _tgtAddr -> do
      -- record all propagations
      recordBlockTransfer blockAddr regs archRegs

    ParsedBranch regs cond _trueAddr _falseAddr -> do
      demandValue blockAddr cond
      -- Compute all transfers
      recordBlockTransfer blockAddr regs archRegs

    ParsedLookupTable _layout regs lookupIdx _vec -> do
      demandValue blockAddr lookupIdx
      -- record all propagations
      recordBlockTransfer blockAddr regs archRegs

    ParsedReturn regs -> do
      let retRegs = functionRetRegs ainfo
      let regDemandSet m (Some r) = do
            rUses <- valueUses (regs^.boundValue r)
            pure $! addDemandFunctionResult r (registerDemandSet rUses) m
      demands <- withAssignmentCache $ foldlM regDemandSet mempty retRegs
      addBlockDemands blockAddr demands
      pure mempty

    ParsedArchTermStmt tstmt regs _nextAddr -> do
       -- Compute effects of terminal statement.
      let e = computeArchTermStmtEffects ainfo tstmt regs

      -- Demand all registers the terminal statement demands.
      do let regUses s (Some r) = addValueUses s (regs^.boundValue r)
         demands <- withAssignmentCache $
           foldlM regUses Set.empty (termRegDemands e)
         addBlockDemands blockAddr $ demandAlways (registerDemandSet demands)
      -- Record registers transered.
      recordBlockTransfer blockAddr regs (termRegTransfers e)
    ParsedTranslateError _ -> do
      -- We ignore demands for translate errors.
      pure mempty
    ClassifyFailure _ _ ->
      -- We ignore demands for classify failure.
      pure mempty

transferRegDemand :: ( MemWidth (ArchAddrWidth arch)
                     , OrdF (ArchReg arch)
                     , ShowF (ArchReg arch)
                     )
                  => FinalRegisterDemands (ArchReg arch)
                  -> DemandSet (ArchReg arch)
                  -- ^ Demands of the start of the next block
                  -> Some (ArchReg arch)
                     -- ^ The register to back propagate
                  -> FunctionArgsM arch ids (DemandSet (ArchReg arch))
transferRegDemand (FRD xfer) s (Some r) =
  case Map.lookup (Some r) xfer of
    Just t -> pure $ mappend s t
    Nothing -> pure s

transferDemands :: ( MemWidth (ArchAddrWidth arch)
                   , OrdF (ArchReg arch)
                   , ShowF (ArchReg arch)
                   )
                => FinalRegisterDemands (ArchReg arch)
                   -- ^ Map from registers to demand sets in
                   -- previous block needed to compute that register.
                -> DemandSet (ArchReg arch)
                   -- ^ Demands of the start of the next block
                -> FunctionArgsM arch ids (DemandSet (ArchReg arch))
transferDemands xfer (DemandSet regs funs) = do
  foldlM (transferRegDemand xfer) (DemandSet Set.empty funs) regs

-- | Given new demands on a register, this back propagates the demands
-- to the predecessor blocks.
calculateOnePred :: ( MemWidth (ArchAddrWidth arch)
                    , OrdF (ArchReg arch)
                    , ShowF (ArchReg arch)
                    )
                 => Map (ArchSegmentOff arch) (FinalRegisterDemands (ArchReg arch))
                    -- ^ Maps the entry point of each block in the function to the
                    -- register demands map for that block.
                 -> BlockDemands (ArchReg arch)
                    -- ^ New demands for this block.
                 -> Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch))
                 -- ^ Maps each block to the demands that have not yet
                 -- been backpropagated to predecessors.
                 -> ArchSegmentOff arch
                    -- ^ Address of the previous block.
                 -> FunctionArgsM arch ids (Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch)))
calculateOnePred xferMap (BD newDemands) pendingMap predAddr = do
  let xfer = xferMap^.ix predAddr

  -- update uses, returning value before this iteration
  BD seenDemands <- use (blockDemandMap . ix predAddr)

  demands' <- traverse (transferDemands xfer) newDemands

  let diff :: OrdF r => DemandSet r -> DemandSet r -> Maybe (DemandSet r)
      diff ds1 ds2 | ds' == mempty = Nothing
                   | otherwise = Just ds'
        where ds' = ds1 `demandSetDifference` ds2

  let d = Map.differenceWith diff demands' seenDemands

  -- If no new entries are seen, then just return pendingMap
  if Map.null d then
    pure $! pendingMap
   else do
    blockDemandMap %= Map.insert predAddr (unionBlockDemands (BD seenDemands) (BD demands'))
    pure $! Map.insertWith unionBlockDemands predAddr (BD d) pendingMap

-- | This back-propagates demands sets from blocks to their
-- predecessors until we each a fixpoint.
calculateLocalFixpoint :: forall arch ids
                       .  ( MemWidth (ArchAddrWidth arch)
                          , OrdF (ArchReg arch)
                          , ShowF (ArchReg arch)
                          )
                       => PredBlockMap arch
                          -- ^ Predecessor block map for function.
                       -> Map (ArchSegmentOff arch) (FinalRegisterDemands (ArchReg arch))
                       -> Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch))
                          -- ^ Maps each block starting address to demands that
                          -- have not yet been back propagated.
                       -> FunctionArgsM arch ids ()
calculateLocalFixpoint predMap xferMap new =
   case Map.maxViewWithKey new of
     Nothing -> pure ()
     Just ((currAddr, newDemands), rest) -> do
       -- propagate new demands bacl to predecessors of this block.
       next <- foldlM (calculateOnePred xferMap newDemands) rest (predMap^.ix currAddr)
       calculateLocalFixpoint predMap xferMap next

-- | Map function entry points that fail to reasons why we could not infer arguments.
type FunctionSummaryFailureMap r = Map (RegSegmentOff r) (FunctionArgAnalysisFailure (RegAddrWidth r))

-- | Intermediate information used to infer global demands.
data FunctionSummaries r = FunctionSummaries {
    _funArgMap       :: !(ArgDemandsMap r)
  , _funResMap       :: !(Map (RegSegmentOff r) (FinalRegisterDemands r))
  , _alwaysDemandMap :: !(Map (RegSegmentOff r) (DemandSet r))
    -- | Map from function starting addresses to reason why initial argument analysis failed.
  , inferenceFails   :: !(FunctionSummaryFailureMap r)
  }

funArgMap :: Simple Lens (FunctionSummaries r) (ArgDemandsMap r)
funArgMap = lens _funArgMap (\s v -> s { _funArgMap = v })

-- | Get the map from function addresses to what results are demanded.
funResMap :: Simple Lens (FunctionSummaries r) (Map (RegSegmentOff r) (FinalRegisterDemands r))
funResMap = lens _funResMap (\s v -> s { _funResMap = v })

-- | Get the map from function adderesses to what results are demanded.
alwaysDemandMap :: Simple Lens (FunctionSummaries r) (Map (RegSegmentOff r)  (DemandSet r))
alwaysDemandMap = lens _alwaysDemandMap (\s v -> s { _alwaysDemandMap = v })

decomposeMap :: OrdF r
             => RegisterSet r
                -- ^ Registers to exclude from always demandMap because the
                -- function ABI guarantees they are only read so that the callee
                -- can prserve their value.
             -> RegSegmentOff r -- ^ Address of this function.
             -> FunctionSummaries r
                -- ^ Current global maps from function addresses to their demands.
             -> DemandType r
             -> DemandSet r
             -> FunctionSummaries r
decomposeMap _ addr acc (DemandFunctionArg f r) v =
  -- Record that if the function @f@ needs register @r@ initialized, then function @addr@
  -- demands @v@.
  acc & funArgMap %~ Map.insertWith (Map.unionWith mappend) (f, Some r) (Map.singleton addr v)
decomposeMap _ addr acc (DemandFunctionResult r) v =
  acc & funResMap %~ Map.insertWith mappend addr (FRD (Map.singleton (Some r) v))
-- Strip out callee saved registers as well.
decomposeMap ds addr acc DemandAlways v =
  let v' = v { registerDemands = registerDemands v `Set.difference` ds }
   in acc & alwaysDemandMap %~ Map.insertWith mappend addr v'

-- | This records the registers a function demands in the global state after
-- being inferred from definition.
recordInferredFunctionDemands :: ArchConstraints arch
                              => ArchDemandInfo arch
                                 -- ^ Contextual information about architecture
                              -> ArchSegmentOff arch
                              -- ^ Function address
                              -> BlockDemands (ArchReg arch)
                              -- ^ Demands of the initial entry block for
                              -- the function after propagation.
                              -> FunctionSummaries (ArchReg arch)
                                 -- ^ Current global state for functions
                              -> FunctionSummaries (ArchReg arch)
recordInferredFunctionDemands ainfo fnAddr (BD fnDemands) globalState =
    -- A function may demand on callee saved register only because
    -- it will store them for use later.  We drop these and the
    -- stack pointer as a demand.
  let spuriousDemands = Set.insert (Some sp_reg) (calleeSavedRegs ainfo)
   in Map.foldlWithKey' (decomposeMap spuriousDemands fnAddr) globalState fnDemands

-- This function computes the following 3 pieces of information:
-- 1. Initial function arguments (ignoring function calls)
-- 2. Function arguments to function arguments
-- 3. Function results to function arguments.
summarizeFunction :: forall arch
              .  ArchConstraints arch
              => FunArgContext arch
              -> FunctionSummaries (ArchReg arch)
                 -- ^ Current function args stat
              -> Some (DiscoveryFunInfo arch)
              -> FunctionSummaries (ArchReg arch)
summarizeFunction ctx acc (Some finfo) = do
  let addr = discoveredFunAddr finfo
  evalFunctionArgsM ctx acc addr $ do
    -- Summarize blocks
    xferMap <- traverse summarizeBlock (finfo^.parsedBlocks)
    -- Propagate block demands until we are done.
    new <- use blockDemandMap
    calculateLocalFixpoint (predBlockMap finfo) xferMap new
    -- Get registers demanded by initial block map.
    entryDemands <- use $ blockDemandMap . ix addr
    -- Record the demands in this function.
    pure $! recordInferredFunctionDemands (archDemandInfo ctx) addr entryDemands acc

-- | Return the demand set for the given registers at the given address.
postRegisterSetDemandsAtAddr :: OrdF r
                             => Map (RegSegmentOff r) (FinalRegisterDemands r)
                             -> RegSegmentOff r
                             -> Set (Some r)
                             -> DemandSet r
postRegisterSetDemandsAtAddr m addr retRegs =
  foldMap (\(Some r) -> postRegisterDemands (m^.ix addr) r) retRegs

-- PERF: we can calculate the return types as we go (instead of doing
-- so at the end).
calculateGlobalFixpoint :: forall r
                        .  OrdF r
                        => FunctionSummaries r
                        -> AddrDemandMap r
calculateGlobalFixpoint s = go (s^.alwaysDemandMap) (s^.alwaysDemandMap)
  where
    argDemandsMap = s^.funArgMap

    go :: AddrDemandMap r
       -> AddrDemandMap r
       -- ^ Maps each function to the new elements
       -- in the demand set that need to be backpropagated to predecessors.
       -> AddrDemandMap r
    go acc new
      | Just ((fun, newDemands), rest) <- Map.maxViewWithKey new =
          let (nexts, acc') = backPropagate acc fun newDemands
           in go acc' (Map.unionWith mappend rest nexts)
      | otherwise = acc

    backPropagate :: AddrDemandMap r
                  -> RegSegmentOff r
                  -> DemandSet r
                  -> (AddrDemandMap r, AddrDemandMap r)
    backPropagate acc fun (DemandSet regs rets) =
      -- We need to push rets through the corresponding functions, and
      -- notify all functions which call fun regs.
      let retDemands :: AddrDemandMap r
          retDemands = Map.mapWithKey (postRegisterSetDemandsAtAddr (s^.funResMap)) rets

          regsDemands :: AddrDemandMap r
          regsDemands =
            Map.unionsWith mappend [ argDemandsMap ^. ix (fun, r) | r <- Set.toList regs ]

          newDemands = Map.unionWith mappend regsDemands retDemands

          -- All this in newDemands but not in acc
          novelDemands = Map.differenceWith diff newDemands acc
      in (novelDemands, Map.unionWith mappend acc novelDemands )

    diff ds1 ds2 =
        let ds' = ds1 `demandSetDifference` ds2 in
        if ds' == mempty then Nothing else Just ds'

-- | This analyzes the discovered functions and returns a mapping from
-- each block to the registers demanded by that blog.
functionDemands :: forall arch
                .  ArchConstraints arch
                => ArchDemandInfo arch
                   -- ^ Architecture-specific demand information.
                -> Memory (ArchAddrWidth arch)
                   -- ^ State of memory for resolving segment offsets.
                -> ResolveCallArgsFn arch
                -> [Some (DiscoveryFunInfo arch)]
                   -- ^ List of function to compute demands for.
                -> (AddrDemandMap (ArchReg arch), FunctionSummaryFailureMap (ArchReg arch))
functionDemands archFns mem resolveCallFn entries = do
  let m0 :: FunctionSummaries (ArchReg arch)
      m0 = FunctionSummaries
           { _funArgMap = Map.empty
           , _funResMap = Map.empty
           , _alwaysDemandMap = Map.empty
           , inferenceFails = Map.empty
           }
  let compAddrSet = Set.fromList $ viewSome discoveredFunAddr <$> entries

  let ctx = FAC { archDemandInfo = archFns
                , ctxMemory = mem
                , computedAddrSet = compAddrSet
                , resolveCallArgs = resolveCallFn
                }
  let summaries = foldl' (summarizeFunction ctx) m0 entries
  (calculateGlobalFixpoint summaries, (inferenceFails summaries))