{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
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


module Data.Macaw.Refinement.UnknownTransfer
  ( symbolicUnkTransferRefinement
  )
where

import Control.Lens
import Data.Macaw.CFG.AssignRhs ( ArchSegmentOff )
import Data.Macaw.Discovery.State ( DiscoveryFunInfo
                                  , DiscoveryState
                                  , ParsedBlock(..)
                                  , ParsedTermStmt(ClassifyFailure)
                                  , blockStatementList
                                  , funInfo
                                  , parsedBlocks
                                  , stmtsTerm
                                  )
import qualified Data.Map as M
import           Data.Parameterized.Some


-- | This is the main entrypoint, which is given the current Discovery
-- information and which attempts to resolve UnknownTransfer
-- classification failures, returning (possibly updated) Discovery
-- information.
symbolicUnkTransferRefinement :: DiscoveryState arch -> DiscoveryState arch
symbolicUnkTransferRefinement = refineTransfers []


-- | The local type used to identify blocks.  Using a local
-- abstraction for this allows this code to be more independent of the
-- underlying block information.
type BlockIdentifier arch = ArchSegmentOff arch

-- | Obtain the local 'BlockIdentifier' value for a block.
blockId :: Some (ParsedBlock arch) -> BlockIdentifier arch
blockId = viewSome pblockAddr

-- | The main loop for transfer discovery refinement.  The first
-- argument is the accumulation of UnknownTransfer failures that
-- refinement has failed for and therefore should not be considered
-- for further refinement.  This is because refinement may reveal new
-- Blocks, which themselves may have unrefined terminators, so this
-- function recurses until there are no more UnknownTransfer failure
-- blocks in the input discovery state that are not also in the
-- failure accumulation array.
refineTransfers :: [BlockIdentifier arch]
                   -- ^ attempted blocks
                -> DiscoveryState arch
                   -- ^ input DiscoveryState
                -> DiscoveryState arch
                   -- ^ Possibly updated DiscoveryState
refineTransfers failedRefine inpDS =
  let unrefineable = flip elem failedRefine . blockId
      unkTransfers = inpDS ^. funInfo
                     . to getAllFunctionsTransfers
                     ^..folded
                     . filtered (not . unrefineable)
      thisUnkTransfer = head unkTransfers
      thisId = blockId thisUnkTransfer
  in if null unkTransfers
     then inpDS
     else case refineBlockTransfer inpDS thisUnkTransfer of
            Nothing    -> refineTransfers (thisId : failedRefine) inpDS
            Just updDS -> refineTransfers failedRefine updDS


getAllFunctionsTransfers :: M.Map (ArchSegmentOff arch)
                                  (Some (DiscoveryFunInfo arch))
                         -> [Some (ParsedBlock arch)]
getAllFunctionsTransfers = concatMap getUnknownTransfers . M.elems


getUnknownTransfers :: (Some (DiscoveryFunInfo arch))
                    -> [Some (ParsedBlock arch)]
getUnknownTransfers (Some fi) =
  Some <$> (filter isUnknownTransfer $ M.elems $ fi ^. parsedBlocks)

isUnknownTransfer :: ParsedBlock arch ids -> Bool
isUnknownTransfer pb =
  case stmtsTerm (blockStatementList pb) of
    ClassifyFailure {} -> True
    _ -> False


-- | This function attempts to use an SMT solver to refine the block
-- transfer.  If the transfer can be resolved, it will update the
-- input DiscoveryState with the new block information (plus any
-- blocks newly discovered via the transfer resolution) and return
-- that.  If it was unable to refine the transfer, it will return
-- Nothing and this block will be added to the "unresolvable" list.
refineBlockTransfer :: DiscoveryState arch
                    -> Some (ParsedBlock arch)
                    -> Maybe (DiscoveryState arch)
refineBlockTransfer _inpDS _pBlk = Nothing
