{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
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
  symbolicUnkTransferRefinement
  ) where

import qualified Control.Lens as L
import           Control.Lens ( (^.) )
import           Control.Monad ( forM )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Scheduler as CS
import qualified Data.Foldable as F
import           Data.List ( sort )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Refinement.FuncBlockUtils as RFU
import qualified Data.Macaw.Refinement.Path as RP
import qualified Data.Macaw.Refinement.SymbolicExecution as RSE
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Map as Map
import           Data.Maybe ( catMaybes, isJust, isNothing )
import           Data.Parameterized.Some ( Some(..), viewSome )
import           GHC.TypeLits

-- | This is the main entrypoint, which is given the current Discovery
-- information and which attempts to resolve UnknownTransfer
-- classification failures, returning (possibly updated) Discovery
-- information.
--
-- See Note [Parallel Evaluation Strategy] for details
symbolicUnkTransferRefinement
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     )
  => RSE.RefinementContext arch
  -> MD.DiscoveryState arch
  -> IO (MD.DiscoveryState arch)
symbolicUnkTransferRefinement context inpDS = do
  -- Set up the evaluation strategy for the work scheduling library.
  --
  -- We use the simple combinator that does not pin workers to specific
  -- capabilities, as these threads spend most of their time waiting on the SMT
  -- solver, so it isn't really important which Haskell thread they use.
  let nCores = CS.ParN (min 1 (fromIntegral (RSE.parallelismFactor (RSE.config context))))
  -- FIXME: Record the unrefinable set so that we don't try to re-refine those
  -- blocks next iteration of refinement
  (solutions, _unrefinable) <- unzip <$> CS.traverseConcurrently nCores (viewSome (refineFunction context)) (allFuns inpDS)
  F.foldlM updateDiscovery inpDS solutions

-- | Returns the list of DiscoveryFunInfo for a DiscoveryState
allFuns :: MD.DiscoveryState arch -> [Some (MD.DiscoveryFunInfo arch)]
allFuns ds = ds ^. MD.funInfo . L.to Map.elems

-- | Attempt to resolve all of the unknown transfers in a block
--
-- Adds solutions for each resolved block into the 'Solutions' object.  It also
-- records the addresses of blocks for which no resolution was possible.
-- Ideally, this record will be used to avoid re-analyzing difficult cases in
-- future refinement iterations.
refineFunction
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     )
  => RSE.RefinementContext arch
  -> MD.DiscoveryFunInfo arch ids
  -> IO ((Some (MD.DiscoveryFunInfo arch), Solutions arch), [Some (RFU.BlockIdentifier arch)])
refineFunction context dfi = do
  -- Find the blocks with unknown transfers
  (solns, unrefinable) <- F.foldlM (refineBlockTransfer context dfi) (mempty, []) (getUnknownTransfers dfi)
  return ((Some dfi, solns), unrefinable)

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
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     )
  => RSE.RefinementContext arch
  -> MD.DiscoveryFunInfo arch ids
  -> (Solutions arch, [Some (RFU.BlockIdentifier arch)])
  -- ^ Solutions accumulated for this function (and blocks marked as unrefinable)
  -> MD.ParsedBlock arch ids
  -- ^ A block ending in an unknown transfer
  -> m (Solutions arch, [Some (RFU.BlockIdentifier arch)])
refineBlockTransfer context fi (solns, unrefinable) blk =
  case RP.pathTo (RFU.blockID blk) $ RP.buildFuncPath fi of
    Nothing -> error "unable to find function path for block" -- internal error
    Just p -> do soln <- refinePath context fi p (RP.pathDepth p) 1
                 case soln of
                   Nothing -> return (solns, Some (RFU.blockID blk) : unrefinable)
                   Just sl ->
                     return (addSolution blk sl solns, unrefinable)

-- | Feed solutions back into the system, updating the 'MD.DiscoveryState' by
-- calling into macaw base.
updateDiscovery :: ( MC.RegisterInfo (MC.ArchReg arch)
                   , KnownNat (MC.ArchAddrWidth arch)
                   , MC.ArchConstraints arch
                   , MonadIO m
                   )
                => MD.DiscoveryState arch
                -> (Some (MD.DiscoveryFunInfo arch), Solutions arch)
                -> m (MD.DiscoveryState arch)
updateDiscovery s0 (Some finfo, solutions) = do
  case solutionValues solutions of
    [] -> return s0
    vals -> return (MD.addDiscoveredFunctionBlockTargets s0 finfo vals)

refinePath :: ( MS.SymArchConstraints arch
              , 16 <= MC.ArchAddrWidth arch
              , MonadIO m
              )
           => RSE.RefinementContext arch
           -> MD.DiscoveryFunInfo arch ids
           -> RP.FuncBlockPath arch ids
           -> Int
           -> Int
           -> m (Maybe (Solution arch))
refinePath context fi path maxlevel numlevels =
  let thispath = RP.takePath numlevels path
      smtEquation = equationFor fi thispath
  in solve context smtEquation >>= \case
       Nothing -> return Nothing -- divergent, stop here
       soln@(Just{}) -> if numlevels >= maxlevel
                          then return soln
                          else refinePath context fi path maxlevel (numlevels + 1)

data Equation arch ids = Equation [[MD.ParsedBlock arch ids]]
newtype Solution arch = Solution [MC.ArchSegmentOff arch]  -- identified transfers
newtype Solutions arch = Solutions (Map.Map (MC.ArchSegmentOff arch) (Solution arch))

instance Semigroup (Solutions arch) where
  Solutions s1 <> Solutions s2 = Solutions (s1 <> s2)

instance Monoid (Solutions arch) where
  mempty = Solutions Map.empty

solutionAddrs :: (MC.RegisterInfo (MC.ArchReg arch))
              => (MC.ArchSegmentOff arch, Solution arch)
              -> (MC.ArchSegmentOff arch, [MC.ArchSegmentOff arch])
solutionAddrs (srcBlockAddr, Solution l) = (srcBlockAddr, l)

solutionValues :: (MC.RegisterInfo (MC.ArchReg arch))
               => Solutions arch
               -> [(MC.ArchSegmentOff arch, [MC.ArchSegmentOff arch])]
solutionValues (Solutions m) = fmap solutionAddrs (Map.toList m)

addSolution :: MD.ParsedBlock arch ids
            -> Solution arch
            -> Solutions arch
            -> Solutions arch
addSolution blk sl (Solutions slns) = Solutions (Map.insert (MD.pblockAddr blk) sl slns)

equationFor :: MD.DiscoveryFunInfo arch ids
            -> RP.FuncBlockPath arch ids
            -> Equation arch ids
equationFor fi p =
  let pTrails = RP.pathForwardTrails p
      pTrailBlocks = map (RFU.getBlock fi) <$> pTrails
  in if and (any (not . isJust) <$> pTrailBlocks)
     then error "did not find requested block in discovery results!" -- internal
       else Equation (catMaybes <$> pTrailBlocks)

-- | Compute a set of solutions for this refinement
--
-- Solutions are currently sorted for convenience, not correctness
solve :: ( MS.SymArchConstraints arch
         , 16 <= MC.ArchAddrWidth arch
         , MonadIO m
         )
      => RSE.RefinementContext arch
      -> Equation arch ids
      -> m (Maybe (Solution arch))
solve context (Equation paths) = do
  possibleModels <- fmap RSE.ipModels <$> forM paths
    (\path -> liftIO $ RSE.smtSolveTransfer context path)
  case any isNothing possibleModels of
    True -> return Nothing
    False -> return (Just (Solution (sort (concat (catMaybes possibleModels)))))

--isBetterSolution :: Solution arch -> Solution arch -> Bool
-- isBetterSolution :: [ArchSegmentOff arch] -> [ArchSegmentOff arch] -> Bool
-- isBetterSolution = (<)

{- Note [Parallel Evaluation Strategy]

The evaluation strategy is structured to support parallelism.  We process
functions in parallel (according to a configurable factor).  Any function with
ClassifyFailures is analyzed in its own thread (all of the ClassifyFailures for
the same function are processed in the same thread).  We then collect all of the
findings for all of the functions and update the discovery state serially.

While this update is constrained to one thread, we are able to use many solver
processes in parallel to do the hard work.

-}
