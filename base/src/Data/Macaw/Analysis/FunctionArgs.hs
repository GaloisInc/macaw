{-| This performs a whole-program analysis to compute which registers
are needed to evaluate different blocks.  It can be used to compute
which registers are needed for function arguments.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
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
  , ComputedRegs(..)
  , DemandSet(..)
  , RegSegmentOff
  , RegisterSet
    -- * Callbacks for architecture-specific information
  , ArchDemandInfo(..)
  , ArchTermStmtRegEffects(..)
  , ComputeArchTermStmtEffects
    -- * Utilities
  , stmtDemandedValues
  ) where

import           Control.Lens
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import qualified Data.ByteString as BS
import           Data.Foldable
import qualified Data.Kind as Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
#if MIN_VERSION_base(4,12,0)
import           Data.Monoid (Ap(Ap, getAp))
#endif

import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.Semigroup ( Semigroup, (<>) )
import           Data.Set (Set)
import qualified Data.Set as Set
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
import           Data.Macaw.Discovery.State
import           Data.Macaw.Types

#if !MIN_VERSION_base(4,12,0)
newtype Ap f a = Ap { getAp :: f a }

instance (Applicative f, Semigroup a) => Semigroup (Ap f a) where
  Ap x <> Ap y = Ap $ (<>) <$> x <*> y

instance (Applicative f,
#if !MIN_VERSION_base(4,11,0)
  Semigroup a,
#endif
  Monoid a) => Monoid (Ap f a) where
  mempty = Ap $ pure mempty
  mappend = (<>)
#endif

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

-- | A set of registrs
type RegisterSet (r :: Type -> Kind.Type) = Set (Some r)

-- | A memory segment offset compatible with the architecture registers.
type RegSegmentOff r = MemSegmentOff (RegAddrWidth r)

-- | This stores the information that is needed to compute a value of some sort.
data DemandSet (r :: Type -> Kind.Type) =
    DemandSet { registerDemands       :: !(RegisterSet r)
                -- | Maps a function address to the registers we need it to return.
              , functionResultDemands :: !(Map (MemSegmentOff (RegAddrWidth r)) (RegisterSet r))
              }

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
  mappend = (<>)

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
    -- | This denotes demands if we need the return value of this
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

type AssignmentCache r ids = Map (Some (AssignId ids)) (RegisterSet r)

-- | Maps each register to the what information is needed to compute
-- the value stored in that register.
newtype FinalRegisterDemands r = FRD (Map (Some r) (DemandSet r))

instance OrdF r => Semigroup (FinalRegisterDemands r) where
  FRD x <> FRD y = FRD (Map.unionWith mappend x y)

instance OrdF r => Monoid (FinalRegisterDemands r) where
  mempty = FRD Map.empty

-- | Describes the effects of an architecture-specific statement
data ArchTermStmtRegEffects arch
   = ArchTermStmtRegEffects { termRegDemands :: ![Some (ArchReg arch)]
                              -- ^ Registers demanded by term statement
                            , termRegTransfers :: [Some (ArchReg arch)]
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

-- | Information about a function whose registers have been resolved.
data ComputedRegs (r :: Type -> Kind.Type) =
  CR { crArguments :: ![Some r]
       -- ^ For each argument, stores the register the argument is
       -- read from.
     , crReturn    :: ![Some r]
       -- ^ Registers that the function provides for return values.
     }

-- | Contextual information to inform argument computation.
data FunArgContext arch = FAC
  { archDemandInfo :: !(ArchDemandInfo arch)
  , ctxMemory :: !(Memory (ArchAddrWidth arch))
    -- ^ State of memory for code analysis
  , computedAddrSet :: !(Set (ArchSegmentOff arch))
    -- ^ Set of addresses that we are current computing addresses for.

  , resolvedAddrs :: !(Map (ArchSegmentOff arch) (ComputedRegs (ArchReg arch)))
    -- ^ Maps addresses whose type has been resolved to the and result
    -- registers.
  , knownSymbolDecls :: !(Map BS.ByteString (ComputedRegs (ArchReg arch)))
    -- ^ Maps symbol names to the argument/return type info for that register.
  }

-- | This is information needed to compute dependencies for a single function.
data FunctionArgsState arch ids = FAS
  { -- | Map from block address to the result demands map for the block.
    _blockTransfer :: !(Map (ArchSegmentOff arch) (FinalRegisterDemands (ArchReg arch)))

    -- | If a demand d is demanded of block address then the block demands S, s.t.
    --   `blockDemandMap ^. at addr ^. at d = Just S1
  , _blockDemandMap    :: !(Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch)))

  -- | Maps each global block label to the set of blocks that have intra-procedural
  -- jumps to that block.  Since the function does not change, we omit the global label
  , _blockPreds     :: !(Map (ArchSegmentOff arch) [ArchSegmentOff arch])
  -- | A cache of the assignments and their deps.  The key is not included
  -- in the set of deps (but probably should be).
  , _assignmentCache :: !(AssignmentCache (ArchReg arch) ids)
    -- | Warnings from summarization in reverse order.
  , reversedWarnings :: [String]
  }

blockTransfer :: Simple Lens (FunctionArgsState arch ids)
                             (Map (ArchSegmentOff arch) (FinalRegisterDemands (ArchReg arch)))
blockTransfer = lens _blockTransfer (\s v -> s { _blockTransfer = v })

blockDemandMap :: Simple Lens (FunctionArgsState arch ids)
                    (Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch)))
blockDemandMap = lens _blockDemandMap (\s v -> s { _blockDemandMap = v })

blockPreds :: Simple Lens (FunctionArgsState arch ids) (Map (ArchSegmentOff arch) [ArchSegmentOff arch])
blockPreds = lens _blockPreds (\s v -> s { _blockPreds = v })

assignmentCache :: Simple Lens (FunctionArgsState arch ids) (AssignmentCache (ArchReg arch) ids)
assignmentCache = lens _assignmentCache (\s v -> s { _assignmentCache = v })

initFunctionArgsState :: [String] -> FunctionArgsState arch ids
initFunctionArgsState prevWarn =
  FAS { _blockTransfer     = Map.empty
      , _blockDemandMap    = Map.empty
      , _blockPreds        = Map.empty
      , _assignmentCache   = Map.empty
      , reversedWarnings   = prevWarn
      }

-- | Monad that runs for computing the dependcies of each block.
type FunctionArgsM arch ids a = StateT (FunctionArgsState arch ids) (Reader (FunArgContext arch)) a

evalFunctionArgsM :: FunArgContext arch
                  -> [String]
                  -> FunctionArgsM arch ids a
                  -> a
evalFunctionArgsM ctx prevWarn m = runReader (evalStateT m (initFunctionArgsState prevWarn)) ctx

-- | Reord a warning in the state
addWarning :: String -> FunctionArgsM arch ids ()
addWarning msg =
  modify $ \s -> s { reversedWarnings = msg : reversedWarnings s }

-- ----------------------------------------------------------------------------------------
-- Phase one functions

-- | This registers a block in the first phase (block discovery).
addIntraproceduralJumpTarget :: ArchConstraints arch
                             => DiscoveryFunInfo arch ids
                             -> ArchSegmentOff arch
                             -> ArchSegmentOff arch
                             -> FunctionArgsM arch ids ()
addIntraproceduralJumpTarget fun_info src dest = do  -- record the edge
  blockPreds %= Map.insertWith (++) dest [src]

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
valueUses (Initial r) = do
  pure $! Set.singleton (Some r)
valueUses _ = do
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
                    .  ( OrdF (ArchReg arch)
                       , FoldableFC (ArchFn arch)
                       , Foldable t
                       )
                    => ArchSegmentOff arch
                       -- ^ Address of current block.
                    -> RegState (ArchReg arch) (Value arch ids)
                       -- ^ Map from registers to values.
                    -> t (Some (ArchReg arch))
                       -- ^ List of registers that subsequent blocks may depend on.
                    -> FunctionArgsM arch ids ()
recordBlockTransfer addr regs regSet = do
  curDemands <- fromMaybe (FRD Map.empty) . Map.lookup addr <$> use blockTransfer
  let doReg :: FinalRegisterDemands (ArchReg arch)
            -> Some (ArchReg arch)
            -> State (AssignmentCache (ArchReg arch) ids)
                     (FinalRegisterDemands (ArchReg arch))
      doReg (FRD m) (Some r) = do
        rs' <- valueUses (regs ^. boundValue r)
        return $! FRD (Map.insertWith mappend (Some r) (registerDemandSet rs') m)
  vs <- withAssignmentCache $ foldlM doReg curDemands regSet
  blockTransfer %= Map.insert addr vs

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
                       => ArchSegmentOff arch
                          -- ^ Address of this block.
                       -> ArchSegmentOff arch
                          -- ^ Address of function we are calling
                       -> RegState (ArchReg arch) (Value arch ids)
                          -- ^ The mapping registers to values when the call occurs.
                       -> FunctionArgsM arch ids ()
linkKnownCallArguments addr faddr regs = do
  -- Associate the demand sets for each potential argument
  -- register with the registers used by faddr.
  argRegs <- asks $ functionArgRegs . archDemandInfo

  -- Get current demands associated with block.
  curDemandMap <- Map.findWithDefault mempty addr <$> use blockDemandMap

  let insertArgRegDemands m (Some r) = do
        vals <- valueUses (regs^. boundValue r)
        pure $! addDemandFunctionArg faddr r (registerDemandSet vals) m

  -- Add demands for computing an argument register value.
  demands <- withAssignmentCache $ foldlM insertArgRegDemands curDemandMap argRegs

  -- Update new demands for address.
  blockDemandMap %= Map.insert addr demands

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
                          -> FunctionArgsM arch ids ()
linkKnownCallReturnValues addr faddr regs mReturnAddr = do
  ainfo <- asks archDemandInfo

  let retRegs = functionRetRegs ainfo

  case mReturnAddr of
    Nothing -> do
      -- Get demands for this block.
      curDemandMap <- Map.findWithDefault mempty addr <$> use blockDemandMap

      -- For each return register @r@, extend @curDemandMap@ so that
      -- to indicate that if a caller demands this function returns
      -- register @r@, then it is demanded that @faddr@ returns
      -- register @r@.
      let addRetRegDemands m (Some r) =
            addDemandFunctionResult r (demandFunctionReturn faddr (Some r)) m
      let nextDemandMap = foldl' addRetRegDemands curDemandMap retRegs
      -- Update new demands for address.
      blockDemandMap %= Map.insert addr nextDemandMap
    Just _ -> do

      -- Record registers available.
      recordBlockTransfer addr regs ([Some sp_reg] ++ Set.toList (calleeSavedRegs ainfo))

      -- Update blockTransfer to indicate that for all potential
      -- return registers that demanding the register
      let linkRetReg (FRD m) sr = FRD (Map.insertWith mappend sr (demandFunctionReturn faddr sr) m)

      let srDemandSet :: FinalRegisterDemands (ArchReg arch)
          srDemandSet = foldl linkRetReg mempty retRegs
      blockTransfer %= Map.insertWith mappend addr srDemandSet


-- A function call is the only block type that results in the
-- generation of function call demands, so we split that aspect out
-- (callee saved are handled in summarizeBlock).
summarizeCall :: forall arch ids
              .  ( FoldableFC (ArchFn arch)
                 , RegisterInfo (ArchReg arch)
                 )
              => ArchSegmentOff arch
                 -- ^ The label for the current block.
              -> RegState (ArchReg arch) (Value arch ids)
                 -- ^ The current mapping from registers to values
              -> Maybe (ArchSegmentOff arch)
                 -- ^ Address to return to or `Nothing` for tail call.
              -> FunctionArgsM arch ids ()
summarizeCall addr finalRegs mReturnAddr = do
  ctx <- ask

  let ipVal = finalRegs^.boundValue ip_reg
  let spVal = finalRegs^.boundValue sp_reg

  -- Record stack pointer and IP is always needed.
  demands <- withAssignmentCache $ foldlM addValueUses Set.empty [ipVal, spVal]
  addBlockDemands addr $ demandAlways (registerDemandSet demands)


  case () of
    -- When we call a function whose arguments we are concurrently trying to compute,
    -- we need to link the fact that if the function demands the
    _ | Just faddr <- valueAsSegmentOff (ctxMemory ctx) ipVal
      , Set.member faddr (computedAddrSet ctx) -> do


      linkKnownCallArguments addr faddr finalRegs
      linkKnownCallReturnValues addr faddr finalRegs mReturnAddr

    _ -> do

      let ainfo = archDemandInfo ctx

      -- Record potential argument registers are always needed.
      let argRegs
            | Just faddr <- valueAsSegmentOff (ctxMemory ctx) ipVal
            , Just cr <- Map.lookup faddr (resolvedAddrs ctx) =
                crArguments cr
            | SymbolValue _ (SymbolRelocation nm _ver) <- ipVal
            , Just cr <- Map.lookup nm (knownSymbolDecls ctx) =
                crArguments cr

            | otherwise =
                functionArgRegs ainfo

      let regUses s (Some r) = addValueUses s (finalRegs^. boundValue r)
      demands <- withAssignmentCache $ foldlM regUses Set.empty argRegs
      addBlockDemands addr $ demandAlways (registerDemandSet demands)

      case mReturnAddr of
        Nothing -> do
          pure ()
        Just _ -> do
          -- Copy callee saved registers and stack pointer across function.
          recordBlockTransfer addr finalRegs (calleeSavedRegs ainfo)


-- | Return values that must be evaluated to execute side effects.
stmtDemandedValues :: DemandContext arch
                   -> Stmt arch ids
                   -> [Some (Value arch ids)]
stmtDemandedValues ctx stmt = demandConstraints ctx $

  case stmt of
    AssignStmt a
      | hasSideEffects ctx (assignRhs a) -> do
          foldMapFC (\v -> [Some v]) (assignRhs a)
      | otherwise ->
          []
    WriteMem addr _ v -> [Some addr, Some v]
    CondWriteMem cond addr _ v -> [Some cond, Some addr, Some v]
    InstructionStart _ _ -> []
    -- Comment statements have no specific value.
    Comment _ -> []
    ExecArchStmt astmt -> foldMapF (\v -> [Some v]) astmt
    ArchState _addr assn -> foldMapF (\v -> [Some v]) assn

-- | This function figures out what the block requires
-- (i.e., addresses that are stored to, and the value stored), along
-- with a map of how demands by successor blocks map back to
-- assignments and registers.
summarizeBlock :: forall arch ids
               .  ArchConstraints arch
               => DiscoveryFunInfo arch ids
               -> ParsedBlock arch ids -- ^ Current block
               -> FunctionArgsM arch ids ()
summarizeBlock interpState b = do
  let addr = pblockAddr b
  -- Add this label to block demand map with empty set.
  addBlockDemands addr mempty

  ctx <- ask
  let ainfo = archDemandInfo ctx
  -- Add all values demanded by non-terminal statements in list.
  mapM_ (mapM_ (\(Some v) -> demandValue addr v) . stmtDemandedValues (demandInfoCtx ainfo))
        (pblockStmts b)
  -- Add values demanded by terminal statements
  case pblockTermStmt b of
    ParsedCall finalRegs mRetAddr -> do
      -- Record the intraprocural jump target for the return address.
      case mRetAddr of
        Nothing -> do
          pure ()
        Just retAddr -> do
          addIntraproceduralJumpTarget interpState addr retAddr

      -- Record the demands based on the call, and add edges between
      -- this note and next nodes.
      summarizeCall addr finalRegs mRetAddr

    PLTStub regs _ sym -> do
      -- Get argument registers if known for symbol.
      let argRegs
            | Just cr <- Map.lookup (versymName sym) (knownSymbolDecls ctx) =
                crArguments cr
            | otherwise =
                functionArgRegs ainfo

      -- Get all registers in arguments that are not defined in regs.
      demands <- withAssignmentCache $ do
        let addRegUses :: RegisterSet (ArchReg arch)
                       -> Some (ArchReg arch)
                       -> State (AssignmentCache (ArchReg arch) ids) (RegisterSet (ArchReg arch))
            addRegUses s (Some r) = do
              case MapF.lookup r regs of
                Just v -> addValueUses s v
                Nothing -> pure $! Set.insert (Some r) s
        foldlM addRegUses Set.empty (functionArgRegs ainfo)
      addBlockDemands addr $ demandAlways $
        registerDemandSet $ demands

    ParsedJump procState tgtAddr -> do
      -- record all propagations
      recordBlockTransfer addr procState archRegs
      addIntraproceduralJumpTarget interpState addr tgtAddr

    ParsedBranch nextRegs cond trueAddr falseAddr -> do
      demandValue addr cond
      -- record all propagations
      let notIP (Some r) = isNothing (testEquality r ip_reg)
      recordBlockTransfer addr nextRegs (filter notIP archRegs)
      addIntraproceduralJumpTarget interpState addr trueAddr
      addIntraproceduralJumpTarget interpState addr falseAddr

    ParsedLookupTable finalRegs lookup_idx vec -> do
      demandValue addr lookup_idx
      -- record all propagations
      recordBlockTransfer addr finalRegs archRegs
      traverse_ (addIntraproceduralJumpTarget interpState addr) vec

    ParsedReturn finalRegs -> do
      let retRegs = functionRetRegs ainfo
      let regDemandSet m (Some r) = do
            regs <- valueUses (finalRegs^.boundValue r)
            pure $! addDemandFunctionResult r (registerDemandSet regs) m
      demands <- withAssignmentCache $ foldlM regDemandSet mempty retRegs
      addBlockDemands addr demands

    ParsedArchTermStmt tstmt finalRegs next_addr -> do
       -- Compute effects of terminal statement.
      let e = computeArchTermStmtEffects ainfo tstmt finalRegs

      -- Demand all registers the terminal statement demands.
      do let regUses s (Some r) = addValueUses s (finalRegs^.boundValue r)
         demands <- withAssignmentCache $
           foldlM regUses Set.empty (termRegDemands e)
         addBlockDemands addr $ demandAlways (registerDemandSet demands)

      recordBlockTransfer addr finalRegs (termRegTransfers e)
      traverse_ (addIntraproceduralJumpTarget interpState addr) next_addr

    ParsedTranslateError _ -> do
      -- We ignore demands for translate errors.
      pure ()
    ClassifyFailure _ ->
      -- We ignore demands for classify failure.
      pure ()


transferRegDemand :: ( MemWidth (ArchAddrWidth arch)
                     , OrdF (ArchReg arch)
                     , ShowF (ArchReg arch)
                     )
                  => ArchSegmentOff arch
                      -- ^ Address of predecessor block.
                  -> ArchSegmentOff arch
                  -- ^ Address of next block
                  -> FinalRegisterDemands (ArchReg arch)
                  -> DemandSet (ArchReg arch)
                  -- ^ Demands of the start of the next block
                  -> Some (ArchReg arch)
                     -- ^ The register to back propagate
                  -> FunctionArgsM arch ids (DemandSet (ArchReg arch))
transferRegDemand prev next (FRD xfer) s (Some r) =
  case Map.lookup (Some r) xfer of
    Just t -> pure $ mappend s t
    Nothing -> do
      addWarning $ "Could not back-propagate " ++ showF r
        ++ " in transition from " ++ show prev
        ++ " to " ++ show next ++ "."
      pure s

transferDemands :: ( MemWidth (ArchAddrWidth arch)
                   , OrdF (ArchReg arch)
                   , ShowF (ArchReg arch)
                   )
                => ArchSegmentOff arch
                   -- ^ Address of predecessor block.
                -> ArchSegmentOff arch
                   -- ^ Address of next block
                -> FinalRegisterDemands (ArchReg arch)
                   -- ^ Final registers demanded from previous block.
                -> DemandSet (ArchReg arch)
                   -- ^ Demands of the start of the next block
                -> FunctionArgsM arch ids (DemandSet (ArchReg arch))
transferDemands prev next xfer (DemandSet regs funs) = do
  foldlM (transferRegDemand prev next xfer) (DemandSet Set.empty funs) regs

-- | Given new demands on a register, this back propagates the demands
-- to the predecessor blocks.
calculateOnePred :: ( MemWidth (ArchAddrWidth arch)
                    , OrdF (ArchReg arch)
                    , ShowF (ArchReg arch)
                    )
                 => ArchSegmentOff arch
                    -- ^ Address of the current block
                 -> BlockDemands (ArchReg arch)
                 -> Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch))
                    -- ^ Current demand map for function
                    --
                    -- Maps block addresses to their demand map.
                 -> ArchSegmentOff arch
                    -- ^ Address of the previous block.
                 -> FunctionArgsM arch ids (Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch)))
calculateOnePred addr (BD newDemands) pendingMap predAddr = do
  xfer   <- use (blockTransfer . ix predAddr)

  -- update uses, returning value before this iteration
  BD seenDemands <- use (blockDemandMap . ix predAddr)

  demands' <- traverse (transferDemands predAddr addr xfer) newDemands

  blockDemandMap %= Map.insert predAddr (unionBlockDemands (BD seenDemands) (BD demands'))


  let diff :: OrdF r => DemandSet r -> DemandSet r -> Maybe (DemandSet r)
      diff ds1 ds2 | ds' == mempty = Nothing
                   | otherwise = Just ds'
        where ds' = ds1 `demandSetDifference` ds2

  let d = Map.differenceWith diff demands' seenDemands
  -- If no new entries are seen, then just return pendingMap
  if Map.null d then
    pure $! pendingMap
   else
    pure $! Map.insertWith unionBlockDemands predAddr (BD d) pendingMap

-- | This updates the block map
calculateLocalFixpoint :: forall arch ids
                       .  ( MemWidth (ArchAddrWidth arch)
                          , OrdF (ArchReg arch)
                          , ShowF (ArchReg arch)
                          )
                       => Map (ArchSegmentOff arch) (BlockDemands (ArchReg arch))
                          -- ^ Maps block addresses to new entries in demand map
                          --
                          -- The function
                       -> FunctionArgsM arch ids ()
calculateLocalFixpoint new =
   case Map.maxViewWithKey new of
     Nothing -> pure ()
     Just ((currAddr, newDemands), rest) -> do
       -- propagate new demands bacl to predecessors of this block.
       preds <- use $ blockPreds . ix currAddr
       next <- foldlM (calculateOnePred currAddr newDemands) rest preds
       calculateLocalFixpoint next

-- | Intermediate information used to infer global demands.
data FunctionSummaries r = FunctionSummaries {
    _funArgMap       :: !(ArgDemandsMap r)
  , _funResMap       :: !(Map (RegSegmentOff r) (FinalRegisterDemands r))
  , _alwaysDemandMap :: !(Map (RegSegmentOff r) (DemandSet r))
  , summaryWarnings :: ![String]
    -- ^ Warnings over summarization.
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
decomposeMap ds addr acc DemandAlways v = do

  let v' = v { registerDemands = registerDemands v `Set.difference` ds }
  acc & alwaysDemandMap %~ Map.insertWith mappend addr v'

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
doOneFunction :: forall arch ids
              .  ArchConstraints arch
              => FunArgContext arch
              -> FunctionSummaries (ArchReg arch)
                 -- ^ Current function args stat
              -> Some (DiscoveryFunInfo arch)
              -> FunctionSummaries (ArchReg arch)
doOneFunction ctx acc (Some finfo) = do
  evalFunctionArgsM ctx (summaryWarnings acc) $ do
    -- Get address of this function
    let addr = discoveredFunAddr finfo

    mapM_ (summarizeBlock finfo) (finfo^.parsedBlocks)

    -- Propagate block demands until we are done.
    new <- use blockDemandMap
    calculateLocalFixpoint new

    -- Get registers demanded by initial block map.
    entryDemands <- use $ blockDemandMap . ix addr

    warn <- gets reversedWarnings

    -- Record the demands in this function.
    let acc1 = acc { summaryWarnings = warn }
    pure $! recordInferredFunctionDemands (archDemandInfo ctx) addr entryDemands acc1

-- PERF: we can calculate the return types as we go (instead of doing
-- so at the end).
calculateGlobalFixpoint :: forall r
                        .  OrdF r
                        => FunctionSummaries r
                        -> (AddrDemandMap r, [String])
calculateGlobalFixpoint s = (go (s^.alwaysDemandMap) (s^.alwaysDemandMap), reverse (summaryWarnings s))
  where
    argDemandsMap    = s^.funArgMap
    resultDemandsMap = s^.funResMap

    go :: AddrDemandMap r
       -> AddrDemandMap r
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
      let goRet :: RegSegmentOff r -> Set (Some r) -> DemandSet r
          goRet addr retRegs =
            foldl (\s r ->
                     let FRD m = resultDemandsMap^.ix addr
                      in mappend s (m^.ix r))
                  mempty
                  retRegs

          retDemands :: AddrDemandMap r
          retDemands = Map.mapWithKey goRet rets

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

-- | This analyzes the discovered functions and returns a mapping from each
-- block to the registers demanded by that blog.
functionDemands :: forall arch
                .  ArchConstraints arch
                => ArchDemandInfo arch
                   -- ^ Architecture-specific demand information.
                -> Map (ArchSegmentOff arch) (ComputedRegs (ArchReg arch))
                -- ^ Maps addresses whose type has been resolved to the and result
                -- registers.
                -> Map BS.ByteString (ComputedRegs (ArchReg arch))
                   -- ^ Known symbol registers.
                -> DiscoveryState arch
                -> (AddrDemandMap (ArchReg arch), [String])
functionDemands archFns addrMap symMap ds =
    calculateGlobalFixpoint (foldl' (doOneFunction ctx) m0 entries)
  where
    notKnown (Some f) = not (Map.member (discoveredFunAddr f) addrMap)
    entries = filter notKnown $ exploredFunctions ds

    m0 :: FunctionSummaries (ArchReg arch)
    m0 = FunctionSummaries
           { _funArgMap = Map.empty
           , _funResMap = Map.empty
           , _alwaysDemandMap = Map.empty
           , summaryWarnings = []
           }

    ctx = FAC { archDemandInfo = archFns
              , ctxMemory = memory ds
              , computedAddrSet = Set.fromList $ viewSome discoveredFunAddr <$> entries
              , resolvedAddrs = addrMap
              , knownSymbolDecls = symMap
              }
