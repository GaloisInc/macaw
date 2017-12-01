{-|
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This performs a whole-program analysis to compute which registers are
needed to evaluate different blocks.  It can be used to compute which
registers are needed for function arguments.
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
import           Control.Monad.State.Strict
import           Data.Foldable as Fold (traverse_)
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Set (Set)
import qualified Data.Set as Set
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.CFG
import           Data.Macaw.CFG.BlockLabel
import           Data.Macaw.Discovery.State
import           Data.Macaw.Fold
import           Data.Macaw.Memory
import           Data.Macaw.Types

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
type RegisterSet (r :: Type -> *) = Set (Some r)

-- | A memory segment offset compatible with the architecture registers.
type RegSegmentOff r = MemSegmentOff (RegAddrWidth r)

-- | This stores the registers needed by a specific address
data DemandSet (r :: Type -> *) =
    DemandSet { registerDemands       :: !(RegisterSet r)
                -- | This maps a function address to the registers
                -- that it needs.
              , functionResultDemands :: !(Map (RegSegmentOff r) (RegisterSet r))
              }

deriving instance (ShowF r, MemWidth (RegAddrWidth r)) => Show (DemandSet r)
deriving instance (TestEquality r) => Eq (DemandSet r)
deriving instance (OrdF r) => Ord (DemandSet r)

instance OrdF r => Monoid (DemandSet r) where
  mempty = DemandSet { registerDemands = Set.empty
                     , functionResultDemands = mempty
                     }
  mappend ds1 ds2 =
    DemandSet { registerDemands = registerDemands ds1 `mappend` registerDemands ds2
              , functionResultDemands =
                  Map.unionWith Set.union (functionResultDemands ds1)
                                          (functionResultDemands ds2)
              }

demandSetDifference :: OrdF r => DemandSet r -> DemandSet r -> DemandSet r
demandSetDifference ds1 ds2 =
  DemandSet (registerDemands ds1 `Set.difference` registerDemands ds2)
            (Map.differenceWith setDiff (functionResultDemands ds1)
                                        (functionResultDemands ds2))
  where
    setDiff s1 s2 =
      let s' = s1 `Set.difference` s2
      in if Set.null s' then Nothing else Just s'

-- | This type is used a key to describe a reason why we demand a particular register.
-- The type r is for a register.
data DemandType r
  -- | This type is for registers that will always be demanded.
  = DemandAlways
  -- | This type is for registers that are demanded if the function at the given address wants
  -- the given register.
  | forall tp. DemandFunctionArg (RegSegmentOff r) (r tp)
    -- | This is a associated with a set of registers that are demanded if the given register is needed
    -- as a return value.
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

type DemandMap r = Map (DemandType r) (DemandSet r)

demandMapUnion :: OrdF r => DemandMap r -> DemandMap r -> DemandMap r
demandMapUnion = Map.unionWith mappend

type AssignmentCache r ids = Map (Some (AssignId ids)) (RegisterSet r)

type ResultDemandsMap r = Map (Some r) (DemandSet r)

-- | Describes the effects of an architecture-specific statement
data ArchTermStmtRegEffects arch
   = ArchTermStmtRegEffects { termRegDemands :: ![Some (ArchReg arch)]
                              -- ^ Registers demanded by term statement
                            , termRegTransfers :: [Some (ArchReg arch)]
                              -- ^ Registers that terminal statement are not modified
                              -- by terminal statement.
                            }

-- | Returns information about the registers needed and modified by a terminal statement
--
-- The first argument is the terminal statement.
--
-- The second is the state of registers when it is executed.
type ComputeArchTermStmtEffects arch ids
   = ArchTermStmt arch ids
   -> RegState (ArchReg arch) (Value arch ids)
   -> ArchTermStmtRegEffects arch

data ArchDemandInfo arch = ArchDemandInfo
     { -- | Registers used as arguments to the function.
       functionArgRegs :: ![Some (ArchReg arch)]
       -- | Registers returned by a function
     , functionRetRegs :: ![Some (ArchReg arch)]
       -- | Registers considered callee saved by functions
     , calleeSavedRegs :: !(Set (Some (ArchReg arch)))
       -- | Compute the effects of a terminal statement on registers.
     , computeArchTermStmtEffects :: !(forall ids . ComputeArchTermStmtEffects arch ids)
     }

-- | This is information needed to compute dependencies for a single function.
data FunctionArgsState arch ids = FAS
  { -- | Holds state about the set of registers that a block uses
    -- (required by this block).
    _blockTransfer :: !(Map (ArchLabel arch) (ResultDemandsMap (ArchReg arch)))

  -- | If a demand d is demanded of block lbl then the block demands S, s.t.
  -- blockDemandMap ^. at lbl ^. at d = Just S
  , _blockDemandMap    :: !(Map (ArchLabel arch) (DemandMap (ArchReg arch)))

  -- | Maps each global block label to the set of blocks that have intra-procedural
  -- jumps to that block.  Since the function does not change, we omit the global label
  , _blockPreds     :: !(Map (ArchLabel arch) [ArchLabel arch])
  -- | A cache of the assignments and their deps.  The key is not included
  -- in the set of deps (but probably should be).
  , _assignmentCache :: !(AssignmentCache (ArchReg arch) ids)

  -- | The set of blocks that we have already visited.
  , _visitedBlocks  :: !(Set (ArchSegmentOff arch))

  -- | The set of blocks we need to consider (should be disjoint from visitedBlocks)
  , _blockFrontier  :: ![ParsedBlock arch ids]
  , archDemandInfo :: !(ArchDemandInfo arch)
  , computedAddrSet :: !(Set (ArchSegmentOff arch))
    -- ^ Set of addresses that are used in function image computation
    -- Other functions are assumed to require all arguments.
  }

blockTransfer :: Simple Lens (FunctionArgsState arch ids)
                             (Map (ArchLabel arch) (ResultDemandsMap (ArchReg arch)))
blockTransfer = lens _blockTransfer (\s v -> s { _blockTransfer = v })

blockDemandMap :: Simple Lens (FunctionArgsState arch ids)
                    (Map (ArchLabel arch) (DemandMap (ArchReg arch)))
blockDemandMap = lens _blockDemandMap (\s v -> s { _blockDemandMap = v })

blockPreds :: Simple Lens (FunctionArgsState arch ids) (Map (ArchLabel arch) [ArchLabel arch])
blockPreds = lens _blockPreds (\s v -> s { _blockPreds = v })

assignmentCache :: Simple Lens (FunctionArgsState arch ids) (AssignmentCache (ArchReg arch) ids)
assignmentCache = lens _assignmentCache (\s v -> s { _assignmentCache = v })

-- |The set of blocks that we have already visited or added to frontier
visitedBlocks :: Simple Lens (FunctionArgsState arch ids) (Set (ArchSegmentOff arch))
visitedBlocks = lens _visitedBlocks (\s v -> s { _visitedBlocks = v })

blockFrontier :: Simple Lens (FunctionArgsState arch ids) [ParsedBlock arch ids]
blockFrontier = lens _blockFrontier (\s v -> s { _blockFrontier = v })

initFunctionArgsState :: ArchDemandInfo arch
                      -> Set (ArchSegmentOff arch)
                      -> FunctionArgsState arch ids
initFunctionArgsState ainfo addrs =
  FAS { _blockTransfer     = Map.empty
      , _blockDemandMap    = Map.empty
      , _blockPreds        = Map.empty
      , _assignmentCache   = Map.empty
      , _visitedBlocks     = Set.empty
      , _blockFrontier     = []
      , archDemandInfo     = ainfo
      , computedAddrSet    = addrs
      }

-- ----------------------------------------------------------------------------------------

type FunctionArgsM arch ids a = State (FunctionArgsState arch ids) a

-- ----------------------------------------------------------------------------------------
-- Phase one functions

-- | This registers a block in the first phase (block discovery).
addIntraproceduralJumpTarget :: ArchConstraints arch
                             => DiscoveryFunInfo arch ids
                             -> ArchLabel arch
                             -> ArchSegmentOff arch
                             -> FunctionArgsM arch ids ()
addIntraproceduralJumpTarget fun_info src_block dest_addr = do  -- record the edge
  let dest = mkRootBlockLabel dest_addr
  blockPreds %= Map.insertWith (++) dest [src_block]
  visited <- use visitedBlocks
  when (Set.notMember dest_addr visited) $ do
    visitedBlocks %= Set.insert dest_addr
    case Map.lookup dest_addr (fun_info^.parsedBlocks) of
      Just dest_reg -> blockFrontier %= (dest_reg:)
      Nothing -> error $ show $
        text "Could not find target block" <+> text (show dest_addr) <$$>
        indent 2 (text "Source:" <$$> pretty src_block)

-- | Compute the input registers that this value depends on
valueUses :: (OrdF (ArchReg arch), FoldableFC (ArchFn arch))
          => Value arch ids tp
          -> FunctionArgsM arch ids (RegisterSet (ArchReg arch))
valueUses v =
  zoom assignmentCache $
            foldValueCached (\_ _    -> mempty)
                            (\_      -> mempty)
                            (\r      -> Set.singleton (Some r))
                            (\_ regs -> regs)
                            v

-- | Record that a block demands the value of certain registers.
recordBlockDemand :: ( OrdF (ArchReg arch)
                     , FoldableFC (ArchFn arch)
                     )
                  => ArchLabel arch
                     -- ^ The current block
                  -> RegState (ArchReg arch) (Value arch ids)
                  -- ^ The current register state
                  -> (forall tp . ArchReg arch tp -> DemandType (ArchReg arch))
                  -> [Some (ArchReg arch)]
                     -- ^ The registers that we need.
                  -> FunctionArgsM arch ids () -- Map (Some N.RegisterName) RegDeps
recordBlockDemand lbl s mk rs = do
  let doReg (Some r) = do
        rs' <- valueUses (s ^. boundValue r)
        return (mk r, DemandSet rs' mempty)
  vs <- mapM doReg rs
  blockDemandMap %= Map.insertWith (Map.unionWith mappend) lbl (Map.fromListWith mappend vs)

-- Figure out the deps of the given registers and update the state for the current label
recordBlockTransfer :: ( OrdF (ArchReg arch)
                       , FoldableFC (ArchFn arch)
                       )
                    => ArchLabel arch
                    -> RegState (ArchReg arch) (Value arch ids)
                    -> [Some (ArchReg arch)]
                    -> FunctionArgsM arch ids () -- Map (Some N.RegisterName) RegDeps
recordBlockTransfer lbl s rs = do
  let doReg (Some r) = do
        rs' <- valueUses (s ^. boundValue r)
        return (Some r, DemandSet rs' mempty)
  vs <- mapM doReg rs
  blockTransfer %= Map.insertWith (Map.unionWith mappend) lbl (Map.fromListWith mappend vs)

-- | A block requires a value, and so we need to remember which
-- registers are required.
demandValue :: (OrdF (ArchReg arch), FoldableFC (ArchFn arch))
            => ArchLabel arch
            -> Value arch ids tp
            -> FunctionArgsM arch ids ()
demandValue lbl v = do
  regs <- valueUses v
  blockDemandMap %= Map.insertWith demandMapUnion lbl
                        (Map.singleton DemandAlways (DemandSet regs mempty))

-- -----------------------------------------------------------------------------
-- Entry point


type AddrDemandMap r = Map (RegSegmentOff r) (DemandSet r)

type ArgDemandsMap r = Map (RegSegmentOff r) (Map (Some r) (AddrDemandMap r))

-- PERF: we can calculate the return types as we go (instead of doing
-- so at the end).
calculateGlobalFixpoint :: forall r
                        .  OrdF r
                        => FunctionArgState r
                        -> AddrDemandMap r
calculateGlobalFixpoint s = go (s^.alwaysDemandMap) (s^.alwaysDemandMap)
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
            mconcat [ resultDemandsMap ^. ix addr ^. ix r | r <- Set.toList retRegs ]

          retDemands :: AddrDemandMap r
          retDemands = Map.mapWithKey goRet rets

          regsDemands :: AddrDemandMap r
          regsDemands =
            Map.unionsWith mappend [ argDemandsMap ^. ix fun ^. ix r | r <- Set.toList regs ]

          newDemands = Map.unionWith mappend regsDemands retDemands

          -- All this in newDemands but not in acc
          novelDemands = Map.differenceWith diff newDemands acc
      in (novelDemands, Map.unionWith mappend acc novelDemands )

    diff ds1 ds2 =
        let ds' = ds1 `demandSetDifference` ds2 in
        if ds' == mempty then Nothing else Just ds'

transferDemands :: OrdF r
                => Map (Some r) (DemandSet r)
                -> DemandSet r
                -> DemandSet r
transferDemands xfer (DemandSet regs funs) =
  -- Using ix here means we ignore any registers we don't know about,
  -- e.g. caller-saved registers after a function call.
  -- FIXME: is this the correct behavior?
  mconcat (DemandSet mempty funs : [ xfer ^. ix r | r <- Set.toList regs ])

-- A function call is the only block type that results in the
-- generation of function call demands, so we split that aspect out
-- (callee saved are handled in summarizeBlock).
summarizeCall :: forall arch ids
              .  ( FoldableFC (ArchFn arch)
                 , RegisterInfo (ArchReg arch)
                 )
              => Memory (ArchAddrWidth arch)
              -> ArchLabel arch
                 -- ^ The label fro the current block.
              -> RegState (ArchReg arch) (Value arch ids)
                 -- ^ The current mapping from registers to values
              -> Bool
                 -- ^ A flag that is set to true for tail calls.
              -> FunctionArgsM arch ids ()
summarizeCall mem lbl proc_state isTailCall = do
  knownAddrs <- gets computedAddrSet
  case asLiteralAddr (proc_state^.boundValue ip_reg) of
    Just faddr0
      | Just faddr <- asSegmentOff mem faddr0
      , Set.member faddr knownAddrs -> do
      -- If a subsequent block demands r, then we note that we want r from
      -- function faddr
      -- FIXME: refactor out Some s
      retRegs <- gets $ functionRetRegs . archDemandInfo
      -- singleton for now, but propagating back will introduce more deps.
      let demandSet sr         = DemandSet mempty (Map.singleton faddr (Set.singleton sr))

      if isTailCall then
        -- tail call, propagate demands for our return regs to the called function
        let propMap = map (\(Some r) -> (DemandFunctionResult r, demandSet (Some r))) retRegs
         in  blockDemandMap %= Map.insertWith (Map.unionWith mappend) lbl (Map.fromList propMap)
       else do
        -- Given a return register sr, this indicates that
        let propResult :: Some (ArchReg arch) -> FunctionArgsM arch ids ()
            propResult sr = do
              --
              let srDemandSet = Map.singleton sr (demandSet sr)
              blockTransfer %= Map.insertWith (Map.unionWith mappend) lbl srDemandSet
        traverse_ propResult retRegs

      -- If a function wants argument register r, then we note that this
      -- block needs the corresponding state values.  Note that we could
      -- do this for _all_ registers, but this should make the summaries somewhat smaller.
      argRegs <- gets $ functionArgRegs . archDemandInfo
      recordBlockDemand lbl proc_state (DemandFunctionArg faddr) argRegs
    _ -> do
      -- In the dynamic case, we just assume all arguments (FIXME: results?)
      argRegs <- gets $ functionArgRegs . archDemandInfo
      recordBlockDemand lbl proc_state (\_ -> DemandAlways) ([Some ip_reg] ++ argRegs)

-- | Return values that must be evaluated to execute side effects.
stmtDemandedValues :: FoldableF (ArchStmt arch)
                   => Stmt arch ids
                   -> [Some (Value arch ids)]
stmtDemandedValues stmt =
  case stmt of
    -- Assignment statements are side effect free so we ignore them.
    AssignStmt a -> case (assignRhs a) of
      EvalApp _ -> []
      SetUndefined _ -> []
      ReadMem addr _ -> [Some addr]
      EvalArchFn _ _ -> []
    WriteMem addr _ v -> [Some addr, Some v]
    -- Place holder statements are unknown.
    PlaceHolderStmt _ _ -> []
    InstructionStart _ _ -> []
    -- Comment statements have no specific value.
    Comment _ -> []
    ExecArchStmt astmt -> foldMapF (\v -> [Some v]) astmt

-- | This function figures out what the block requires
-- (i.e., addresses that are stored to, and the value stored), along
-- with a map of how demands by successor blocks map back to
-- assignments and registers.
summarizeBlock :: forall arch ids
               .  ArchConstraints arch
               => Memory (ArchAddrWidth arch)
               -> DiscoveryFunInfo arch ids
               -> ArchSegmentOff arch -- ^ Address of the code.
               -> StatementList arch ids -- ^ Current block
               -> FunctionArgsM arch ids ()
summarizeBlock mem interp_state addr stmts = do
  let lbl = GeneratedBlock addr (stmtsIdent stmts)
  -- Add this label to block demand map with empty set.
  blockDemandMap %= Map.insertWith demandMapUnion lbl mempty

  -- Add all values demanded by non-terminal statements in list.
  mapM_ (\(Some v) -> demandValue lbl v)
        (concatMap stmtDemandedValues (stmtsNonterm stmts))
  -- Add values demanded by terminal statements
  case stmtsTerm stmts of
    ParsedTranslateError _ -> do
      -- We ignore demands for translate errors.
      pure ()
    ClassifyFailure _ ->
      -- We ignore demands for classify failure.
      pure ()

    ParsedIte c tblock fblock -> do
      -- Demand condition then summarize recursive blocks.
      demandValue lbl c
      summarizeBlock mem interp_state addr tblock
      summarizeBlock mem interp_state addr fblock

    ParsedCall proc_state m_ret_addr -> do
      case m_ret_addr of
        Nothing -> do
          summarizeCall mem lbl proc_state True
        Just ret_addr -> do
          summarizeCall mem lbl proc_state False
          addIntraproceduralJumpTarget interp_state lbl ret_addr
          callRegs <- gets $ calleeSavedRegs . archDemandInfo
          recordBlockTransfer lbl proc_state ([Some sp_reg] ++ Set.toList callRegs)

    ParsedJump proc_state tgt_addr -> do
      -- record all propagations
      recordBlockTransfer lbl proc_state archRegs
      addIntraproceduralJumpTarget interp_state lbl tgt_addr

    ParsedReturn proc_state -> do
      retRegs <- gets $ functionRetRegs . archDemandInfo
      recordBlockDemand lbl proc_state DemandFunctionResult retRegs

    ParsedArchTermStmt tstmt proc_state next_addr -> do
      effFn <- gets $ computeArchTermStmtEffects . archDemandInfo
      let e = effFn tstmt proc_state
      recordBlockDemand   lbl proc_state (\_ -> DemandAlways) (termRegDemands e)
      recordBlockTransfer lbl proc_state (termRegTransfers e)
      traverse_ (addIntraproceduralJumpTarget interp_state lbl) next_addr

    ParsedLookupTable proc_state lookup_idx vec -> do
      demandValue lbl lookup_idx
      -- record all propagations
      recordBlockTransfer lbl proc_state archRegs
      traverse_ (addIntraproceduralJumpTarget interp_state lbl) vec

-- | Explore states until we have reached end of frontier.
summarizeIter :: ArchConstraints arch
              => Memory (ArchAddrWidth arch)
              -> DiscoveryFunInfo arch ids
              -> FunctionArgsM arch ids ()
summarizeIter mem ist = do
  fnFrontier <- use blockFrontier
  case fnFrontier of
    [] ->
      return ()
    reg : frontier' -> do
      blockFrontier .= frontier'
      summarizeBlock mem ist (pblockAddr reg) (blockStatementList reg)
      summarizeIter mem ist

calculateOnePred :: (OrdF (ArchReg arch))
                 => DemandMap (ArchReg arch)
                 -> ArchLabel arch
                 -> FunctionArgsM arch ids (ArchLabel arch, DemandMap (ArchReg arch))
calculateOnePred newDemands predLbl = do
  xfer   <- use (blockTransfer . ix predLbl)

  let demands' = transferDemands xfer <$> newDemands
      lbl' = rootBlockLabel predLbl

  -- update uses, returning value before this iteration
  seenDemands <- use (blockDemandMap . ix lbl')
  blockDemandMap . at lbl' .= Just (Map.unionWith mappend demands' seenDemands)
  -- seenDemands <- blockDemandMap . ix lbl' <<%= demandMapUnion demands'


  let diff :: OrdF r => DemandSet r -> DemandSet r -> Maybe (DemandSet r)
      diff ds1 ds2 | ds' == mempty = Nothing
                   | otherwise = Just ds'
        where ds' = ds1 `demandSetDifference` ds2

  return (lbl', Map.differenceWith diff demands' seenDemands)


calculateLocalFixpoint :: forall arch ids
                       .  OrdF (ArchReg arch)
                       => Map (ArchLabel arch) (DemandMap (ArchReg arch))
                       -> FunctionArgsM arch ids ()
calculateLocalFixpoint new =
   case Map.maxViewWithKey new of
     Just ((currLbl, newDemands), rest) -> do
       -- propagate backwards any new demands to the predecessors
       preds <- use $ blockPreds . ix (rootBlockLabel currLbl)
       nexts <- filter (not . Map.null . snd) <$> mapM (calculateOnePred newDemands) preds
       calculateLocalFixpoint (Map.unionWith demandMapUnion rest
                                  (Map.fromListWith demandMapUnion nexts))
     Nothing -> return ()


data FunctionArgState r = FunctionArgState {
    _funArgMap       :: !(ArgDemandsMap r)
  , _funResMap       :: !(Map (RegSegmentOff r) (ResultDemandsMap r))
  , _alwaysDemandMap :: !(Map (RegSegmentOff r) (DemandSet r))
  }

funArgMap :: Simple Lens (FunctionArgState r) (ArgDemandsMap r)
funArgMap = lens _funArgMap (\s v -> s { _funArgMap = v })

-- | Get the map from function addresses to what results are demanded.
funResMap :: Simple Lens (FunctionArgState r) (Map (RegSegmentOff r) (ResultDemandsMap r))
funResMap = lens _funResMap (\s v -> s { _funResMap = v })

-- | Get the map from function adderesses to what results are demanded.
alwaysDemandMap :: Simple Lens (FunctionArgState r) (Map (RegSegmentOff r)  (DemandSet r))
alwaysDemandMap = lens _alwaysDemandMap (\s v -> s { _alwaysDemandMap = v })

decomposeMap :: OrdF r
             => DemandSet r
             -> RegSegmentOff r
             -> FunctionArgState r
             -> DemandType r
             -> DemandSet r
             -> FunctionArgState r
decomposeMap _ addr acc (DemandFunctionArg f r) v =
  -- FIXME: A bit of an awkward datatype ...
  let m = Map.singleton (Some r) (Map.singleton addr v)
   in acc & funArgMap %~ Map.insertWith (Map.unionWith (Map.unionWith mappend)) f m
decomposeMap _ addr acc (DemandFunctionResult r) v =
  acc & funResMap %~ Map.insertWith (Map.unionWith mappend) addr (Map.singleton (Some r) v)
-- Strip out callee saved registers as well.
decomposeMap ds addr acc DemandAlways v =
  acc & alwaysDemandMap %~ Map.insertWith mappend addr (v `demandSetDifference` ds)

-- This function computes the following 3 pieces of information:
-- 1. Initial function arguments (ignoring function calls)
-- 2. Function arguments to function arguments
-- 3. Function results to function arguments.
doOneFunction :: forall arch ids
              .  ArchConstraints arch
              => ArchDemandInfo arch
              -> Set (ArchSegmentOff arch)
              -> DiscoveryState arch
              -> FunctionArgState (ArchReg arch)
              -> DiscoveryFunInfo arch ids
              -> FunctionArgState (ArchReg arch)
doOneFunction archFns addrs ist0 acc ist = do
  flip evalState (initFunctionArgsState archFns addrs) $ do
    let addr = discoveredFunAddr ist
    let lbl0 = mkRootBlockLabel addr
    -- Run the first phase (block summarization)
    visitedBlocks .= Set.singleton addr

    case Map.lookup addr (ist^.parsedBlocks) of
      Just b -> blockFrontier .= [b]
      Nothing -> error $ "Could not find initial block for " ++ show addr

    summarizeIter (memory ist0) ist
    -- propagate back uses
    new <- use blockDemandMap

    -- debugM DFunctionArgs (">>>>>>>>>>>>>>>>>>>>>>>>" ++ (showHex addr "" ))
    -- debugM' DFunctionArgs (ppMap (text . show) (ppMap (text . show) (text . show)) new)
    -- debugM DFunctionArgs ("------------------------" ++ (showHex addr "" ))
    -- xfer <- use blockTransfer
    -- debugM' DFunctionArgs (ppMap (text . show) (ppMap (text . show) (text . show)) xfer)

    calculateLocalFixpoint new
    -- summary for entry block has what we want.
    -- m <- use (blockDemandMap . ix lbl0)
    -- debugM DFunctionArgs ("*************************"  ++ (showHex addr "" ))
    -- debugM' DFunctionArgs (ppMap (text . show) (text . show) m)
    -- debugM DFunctionArgs ("<<<<<<<<<<<<<<<<<<<<<<<<<" ++ (showHex addr "" ))

    funDemands <- use (blockDemandMap . ix lbl0)

    -- A function may demand a callee saved register as it will store
    -- it onto the stack in order to use it later.  This will get
    -- recorded as a use, which is erroneous, so we strip out any
    -- reference to them here.
    callRegs <- gets $ calleeSavedRegs . archDemandInfo
    let calleeDemandSet = DemandSet { registerDemands =
                                        Set.insert (Some sp_reg) callRegs
                                    , functionResultDemands = mempty
                                    }

    return (Map.foldlWithKey' (decomposeMap calleeDemandSet addr) acc funDemands)


-- | This analyzes the discovered functions and returns a mapping from each
functionDemands :: forall arch
                .  ArchConstraints arch
                => ArchDemandInfo arch
                -> DiscoveryState arch
                -> Map (ArchSegmentOff arch) (DemandSet (ArchReg arch))
functionDemands archFns info = calculateGlobalFixpoint (foldl f m0 entries)
  where
    entries =  exploredFunctions info

    addrs = Set.fromList $ viewSome discoveredFunAddr <$> entries

    m0 = FunctionArgState Map.empty Map.empty Map.empty

    f mi (Some finfo) = doOneFunction archFns addrs info mi finfo

{-

debugPrintMap :: DiscoveryState X86_64 -> Map (MemSegmentOff 64) FunctionType -> String
debugPrintMap ist m = "Arguments: \n\t" ++ intercalate "\n\t" (Map.elems comb)
  where -- FIXME: ignores those functions we don't have names for.
        comb = Map.intersectionWith doOne (symbolAddrsAsMap (symbolNames ist)) m
        doOne n ft = BSC.unpack n ++ ": " ++ show (pretty ft)
-}
