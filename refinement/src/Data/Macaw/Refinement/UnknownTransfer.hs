{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
-- | This module uses symbolic evaluation to refine the discovered CFG
-- and resolve unknown transfer classify failures.
--
-- One of the primary refinements possible via this module is the
-- ability to determine transfer targets that were previously
-- undiscoverable.
--
-- For example (roughly tests/samples/switching.c):
--
-- > int retval(int n) {
-- >   switch (n) {
-- >     case 0: ...;
-- >     case 1: ...;
-- >     case 3: ...;
-- >     default: 0;
-- >   }
-- > }
--
-- In the above, the body of each case is relatively small and similar
-- to the others, so the compiler decides not to generate a series of
-- 'cmp n, VAL; jeq CASETGT' instructions, but instead computes an
-- offset based on the maximum size of each case body * n and adds
-- that to the current address.
--
-- discovery:
--   block 1 "setup": terminate with: ite r28 @default-handler @cases-handler
--   block 2 "cases-handler": calculates jump offset for case values, CLASSIFY FAILURE: unknown transfer
--   block 3 "default-handler": terminate with return
--
-- In this example, the jump offset for case values is range-limited
-- by block 1, but block 2 doesn't see that, and also because of that
-- the block(s) corresponding to the case conditions are not
-- discovered.  The goal of the code in this module is to improve
-- this, using SMT analysis.
--
-- First, a What4 formula is generated for block 2 and this is
-- provided to Crucible to identify possible jump targets.  The result
-- should be a nearly infinite number of targets (every "case body
-- size" offset), which Macaw could constrain to the valid text region
-- (although the jumps beyond the text region could arguably be
-- flagged as errors).
--
-- However, by adding the precursor block (block 1) and computing the
-- SMT formula for block 1 + block2, the result of the jump is only
-- the actual case targets, and thus this is a smaller solution (and
-- therefore better) than the previous step.
--
-- The algorithm should continue to iterate back through the blocks to
-- achieve better and better (i.e. smaller) solutions until reaching
-- the entry point of the function itself, or until reaching a point
-- where the solution symbolically diverges (e.g. a loop with a
-- variable exit condition).
--
-- It might be considered an optimization to simply skip the
-- iterations and try to solve from the start of the function to the
-- unknown transfer point, but if there are symbolically-divergent
-- loops in that path the result will be unconstrained (see Note 1).
--
-- In the worst case, the SMT analysis is unable to further refine the
-- information and this block is still noted as an unkown transfer, so
-- it has not worsened the analysis, even though it has not improved
-- it.
--
-- If the refinement does yield a smaller set of functions, that can
-- be identified as the valid targets from this block (e.g. a nested
-- ite), and additionally those targets should be subject to further
-- discovery by Macaw.
--
-- --------------------
-- Note 1: It's theoretically possible that the loop would affect the
-- constraints, but in practice this is fairly unrealistic.  A
-- completely unbounded jump is unlikely to ever be generated for
-- valid compiled C code:
--
-- > int jumpto(int n) {
-- >    (void)(*funcaddr)() = n * 32 + &jumpto;   // unrealistic
-- >    (*funcaddr)();
-- > }
--
-- A jump computation is generally only to target symbols known to the
-- C compiler, and while a section of code that cannot be symbolically
-- resolved (e.g. a symbolically-divergent loop) might *constrain* the
-- target set, the analysis of the portion following the loop should
-- reveal the total set of valid targets:
--
-- > int jumpfor(int n, int l) {
-- >    (int)(*funcs)()[6] = { &jumptgt1, &jumptgt2, ... };
-- >    int tgtnum = n % 3;
-- >    for (int j = 0; j < l; j++) {
-- >      if (j ^ n == 5)
-- >        tgtnum *= 2;
-- >    }
-- >    return (*(funcs[tgtnum]))();
-- > }
--
-- In this case, we hope to discover that the target of the jumps is
-- constrained to the entries in the funcs array, even though the loop
-- cannot be evaluated.


module Data.Macaw.Refinement.UnknownTransfer (
  RefinementFindings,
  symbolicUnkTransferRefinement,
  RefinementInfo(..),
  findingsInfo
  ) where

import qualified Control.Lens as L
import           Control.Lens ( (^.) )
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class ( MonadIO )
import qualified Control.Monad.IO.Unlift as MU
import qualified Control.Scheduler as CS
import qualified Data.Foldable as F
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Refinement.FuncBlockUtils as RFU
import           Data.Macaw.Refinement.Logging ( RefinementLog(..) )
import qualified Data.Macaw.Refinement.Path as RP
import qualified Data.Macaw.Refinement.SymbolicExecution as RSE
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Map as Map
import           Data.Maybe ( isJust, isNothing )
import           Data.Parameterized.Some ( Some(..), viewSome )
import qualified Data.Set as S
import           GHC.TypeLits
import qualified Lumberjack as LJ

-- | This is the main entrypoint, which is given the current Discovery
-- information and which attempts to resolve UnknownTransfer
-- classification failures, returning (possibly updated) Discovery
-- information.
--
-- We thread through previous findings ('RefinementFindings') so that we can
-- avoid re-analyzing code that we can't reason about.
--
-- See Note [Parallel Evaluation Strategy] for details
symbolicUnkTransferRefinement
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     )
  => RSE.RefinementContext arch
  -- ^ Configuration
  -> RefinementFindings arch
  -- ^ Previous results from refinement (to avoid re-analysis)
  -> MD.DiscoveryState arch
  -- ^ The state from macaw to refine
  -> m (MD.DiscoveryState arch, RefinementFindings arch)
symbolicUnkTransferRefinement context oldFindings inpDS = do
  -- Set up the evaluation strategy for the work scheduling library.
  --
  -- We use the simple combinator that does not pin workers to specific
  -- capabilities, as these threads spend most of their time waiting on the SMT
  -- solver, so it isn't really important which Haskell thread they use.
  let nCores = CS.ParN (max 1 (fromIntegral (RSE.parallelismFactor (RSE.config context))))
  funcSolutions <- CS.traverseConcurrently nCores (viewSome (refineFunction context oldFindings)) (allFuns inpDS)
  outDS <- F.foldlM updateDiscovery inpDS funcSolutions
  let findings = oldFindings <> mconcat (fmap (solutionsToFindings . snd) funcSolutions)
  return (outDS, findings)


-- | Attempt to resolve all of the unknown transfers in a block
--
-- Adds solutions for each resolved block into the 'Solutions' object.  It also
-- records the addresses of blocks for which no resolution was possible.
-- Ideally, this record will be used to avoid re-analyzing difficult cases in
-- future refinement iterations.
refineFunction
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     )
  => RSE.RefinementContext arch
  -> RefinementFindings arch
  -> MD.DiscoveryFunInfo arch ids
  -> m (Some (MD.DiscoveryFunInfo arch), Solutions arch)
refineFunction context oldFindings dfi = do
  -- Find the blocks with unknown transfers
  solns <- F.foldlM (refineBlockTransfer context oldFindings dfi) mempty (getUnknownTransfers dfi)
  return (Some dfi, solns)

getUnknownTransfers :: MD.DiscoveryFunInfo arch ids
                    -> [MD.ParsedBlock arch ids]
getUnknownTransfers fi =
  filter (isUnknownTransfer fi) (Map.elems (fi ^. MD.parsedBlocks))

isUnknownTransfer :: MD.DiscoveryFunInfo arch ids -> MD.ParsedBlock arch ids -> Bool
isUnknownTransfer fi pb =
  case MD.pblockTermStmt pb of
    MD.ClassifyFailure {} ->
      isNothing (lookup (MD.pblockAddr pb) (MD.discoveredClassifyFailureResolutions fi))
    _ -> False

-- | Discover refinements of control flow for blocks ending in ClassifyFailure
--
-- This function does the hard work: it constructs a set of paths from the
-- ClassifyFailure back as far toward the function start as is possible without
-- creating a loop.  It then uses symbolic execution to generate models of the
-- instruction pointer at the ClassifyFailure (solutions).
--
-- If it cannot find any solutions for a given ClassifyFailure, it marks the
-- block as unrefinable so that we can avoid re-analyzing it in subsequent
-- iterations.
--
-- The caller is expected to update the DiscoveryState with any discovered
-- solutions.
refineBlockTransfer
  :: forall arch m ids
    . ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MU.MonadUnliftIO m
     , LJ.HasLog (RefinementLog arch) m
     , X.MonadThrow m
     )
  => RSE.RefinementContext arch
  -> RefinementFindings arch
  -> MD.DiscoveryFunInfo arch ids
  -> Solutions arch
  -- ^ Solutions accumulated for this function (and blocks marked as unrefinable)
  -> MD.ParsedBlock arch ids
  -- ^ A block ending in an unknown transfer
  -> m (Solutions arch)
refineBlockTransfer context oldFindings fi solns blk
  | haveFindingsFor oldFindings blk = return solns
  | otherwise = do
    LJ.writeLogM (RefiningTransferAt @arch (MD.pblockAddr blk))
    let cfg = RP.mkPartialCFG fi
    let slices = RP.cfgPathsTo (RFU.blockID blk) cfg
    possibleSolutions <- mapM (refineSlice context) slices
    return (addSolution blk possibleSolutions solns)

haveFindingsFor :: RefinementFindings arch -> MD.ParsedBlock arch ids -> Bool
haveFindingsFor (RefinementFindings m) blk =
  isJust (Map.lookup (MD.pblockAddr blk) m)

asIPModels :: IPModelsFor arch a -> Maybe [a]
asIPModels (IPModelsFor _ ipm) =
  case ipm of
    RSE.Models ms -> Just ms
    _ -> Nothing

-- | Feed solutions back into the system, updating the 'MD.DiscoveryState' by
-- calling into macaw base.
updateDiscovery :: ( MC.RegisterInfo (MC.ArchReg arch)
                   , KnownNat (MC.ArchAddrWidth arch)
                   , MC.ArchConstraints arch
                   , MonadIO m
                   , LJ.HasLog (RefinementLog arch) m
                   )
                => MD.DiscoveryState arch
                -> (Some (MD.DiscoveryFunInfo arch), Solutions arch)
                -> m (MD.DiscoveryState arch)
updateDiscovery s0 (Some finfo, solutions) = do
  case solutionValues solutions of
    Nothing -> return s0
    -- Consider making this an error, as it means some invariants were violated
    Just [] -> return s0
    Just vals -> return (MD.addDiscoveredFunctionBlockTargets s0 finfo vals)

refineSlice :: ( MS.SymArchConstraints arch
               , 16 <=  MC.ArchAddrWidth arch
               , MU.MonadUnliftIO m
               , LJ.HasLog (RefinementLog arch) m
               , X.MonadThrow m
               )
            => RSE.RefinementContext arch
            -> RP.CFGSlice arch ids
            -> m (IPModelsFor arch (MC.ArchSegmentOff arch))
refineSlice context slice = solve context slice

-- | The set (list) of models found for each basic block
--
-- Currently, the intent is that a solutions object represents solutions within
-- a single function.
--
-- NOTE: The IPModels structure can contain embedded errors, so it should be
-- processed before use to ensure that solutions are all valid before applying
-- them to a DiscoveryState.
newtype Solutions arch = Solutions (Map.Map (MC.ArchSegmentOff arch) [IPModelsFor arch (MC.ArchSegmentOff arch)])

instance Semigroup (Solutions arch) where
  Solutions s1 <> Solutions s2 = Solutions (s1 <> s2)

instance Monoid (Solutions arch) where
  mempty = Solutions Map.empty

solutionValues :: (MC.RegisterInfo (MC.ArchReg arch))
               => Solutions arch
               -> Maybe [(MC.ArchSegmentOff arch, [MC.ArchSegmentOff arch])]
solutionValues (Solutions m) = mapM addrsFromIPModel (Map.toList m)
  where
    addrsFromIPModel (srcBlockAddr, models) = do
      addrs <- mapM asIPModels models
      return (srcBlockAddr, unique (concat addrs))

    unique = S.toList . S.fromList

addSolution :: MD.ParsedBlock arch ids
            -> [IPModelsFor arch (MC.ArchSegmentOff arch)]
            -> Solutions arch
            -> Solutions arch
addSolution blk sl (Solutions slns) = Solutions (Map.insert (MD.pblockAddr blk) sl slns)

-- | Compute a set of solutions for this refinement
solve :: ( MS.SymArchConstraints arch
         , 16 <= MC.ArchAddrWidth arch
         , MU.MonadUnliftIO m
         , LJ.HasLog (RefinementLog arch) m
         , X.MonadThrow m
         )
      => RSE.RefinementContext arch
      -> RP.CFGSlice arch ids
      -> m (IPModelsFor arch (MC.ArchSegmentOff arch))
solve context slice = do
  models <- RSE.smtSolveTransfer context slice
  return (IPModelsFor (RP.sliceAddress slice) models)

-- | Models of the instruction pointer paired with the address of the block
-- containing the unresolved transfer the models are for
data IPModelsFor arch a =
  IPModelsFor (MC.ArchSegmentOff arch) (RSE.IPModels a)
  deriving (Eq)

-- | This is isomorphic to 'Solutions', but contains results for multiple
-- functions (rather than only for a single function)
--
-- We keep this so that we can avoid re-processing the same block again on later
-- iterations and also record reasons for each failure.  Note that successes are
-- also included so that we don't re-analyze successfully-refined blocks.
newtype RefinementFindings arch =
  RefinementFindings (Map.Map (MC.ArchSegmentOff arch) [IPModelsFor arch (MC.ArchSegmentOff arch)])
  deriving (Eq)

instance Semigroup (RefinementFindings arch) where
  RefinementFindings m1 <> RefinementFindings m2 = RefinementFindings (m1 <> m2)

instance Monoid (RefinementFindings arch) where
  mempty = RefinementFindings Map.empty

-- | Lift 'Solutions' into 'RefinementFindings' so that we can join them
-- together into whole-program results from single function results
solutionsToFindings :: Solutions arch -> RefinementFindings arch
solutionsToFindings (Solutions m) = RefinementFindings m

-- | Returns the list of DiscoveryFunInfo for a DiscoveryState
allFuns :: MD.DiscoveryState arch -> [Some (MD.DiscoveryFunInfo arch)]
allFuns ds = ds ^. MD.funInfo . L.to Map.elems

-- | A summary of refinement failures
data RefinementInfo arch =
  RefinementInfo { refinementTimeouts :: [MC.ArchSegmentOff arch]
                 -- ^ The addresses of blocks with unresolved control flow that
                 -- could not be resolved due to timeouts
                 , refinementSpurious :: [MC.ArchSegmentOff arch]
                 -- ^ The addresses of blocks with unresolved control flow that
                 -- are under-constrained and produced only spurious models
                 , refinementErrors :: [(MC.ArchSegmentOff arch, String)]
                 -- ^ Errors encountered during refinement
                 , refinementNoModels :: [MC.ArchSegmentOff arch]
                 -- ^ Refinements that produced no models at all
                 }

-- | Project 'RefinementFindings' into a user-visible structure
--
-- Currently, this discards successes under the premise that they are obvious
-- from the 'DiscoveryState'.  It might be useful to just summarize successes
-- here.
findingsInfo :: RefinementFindings arch -> RefinementInfo arch
findingsInfo (RefinementFindings findings) =
  RefinementInfo { refinementTimeouts = timeouts
                 , refinementSpurious = spurious
                 , refinementErrors = errors
                 , refinementNoModels = none
                 }
  where
    (timeouts, spurious, errors, none) = F.foldl' collectModels ([], [], [], []) (Map.elems findings)
    collectModels = F.foldl' collectModel
    collectModel acc@(t, s, e, n) (IPModelsFor addr ipModel) =
      case ipModel of
        RSE.Timeout -> (addr : t, s, e, n)
        RSE.SpuriousModels -> (t, addr : s, e, n)
        RSE.Error msg -> (t, s, (addr, msg) : e, n)
        RSE.NoModels -> (t, s, e, addr : n)
        RSE.Models {} -> acc

{- Note [Parallel Evaluation Strategy]

The evaluation strategy is structured to support parallelism.  We process
functions in parallel (according to a configurable factor).  Any function with
ClassifyFailures is analyzed in its own thread (all of the ClassifyFailures for
the same function are processed in the same thread).  We then collect all of the
findings for all of the functions and update the discovery state serially.

While this update is constrained to one thread, we are able to use many solver
processes in parallel to do the hard work.

-}
