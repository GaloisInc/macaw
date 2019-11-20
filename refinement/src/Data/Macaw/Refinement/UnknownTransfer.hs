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
import           Data.List ( sort )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.CFG.AssignRhs ( ArchSegmentOff )
import           Data.Macaw.CFG.Block ( TermStmt(..) )
import qualified Data.Macaw.CFG.Rewriter as RW
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Refinement.FuncBlockUtils as RFU
import qualified Data.Macaw.Refinement.Path as RP
import qualified Data.Macaw.Refinement.SymbolicExecution as RSE
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Parameterized.Some
import           GHC.TypeLits
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))


-- | This is the main entrypoint, which is given the current Discovery
-- information and which attempts to resolve UnknownTransfer
-- classification failures, returning (possibly updated) Discovery
-- information.
symbolicUnkTransferRefinement
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> MD.DiscoveryState arch
  -> m (MD.DiscoveryState arch)
symbolicUnkTransferRefinement context inpDS =
  refineFunctions context inpDS mempty $ allFuns inpDS


-- | Returns the list of DiscoveryFunInfo for a DiscoveryState
allFuns :: MD.DiscoveryState arch -> [Some (MD.DiscoveryFunInfo arch)]
allFuns ds = ds ^. MD.funInfo . L.to Map.elems


-- | This iterates through the functions in the DiscoveryState to find
-- those which have transfer failures and attempts to refine the
-- transfer failure.  There are three cases:
--
--  1. The function has no transfer failures
--  2. The function has a transfer failure, but cannot be refined
--  3. The function has a transfer failure that was refined
--
-- For both #1 and #2, the action is to move to the next function.
-- For #3, the refinement process had to re-perform discovery (the
-- refinement may have added new previously undiscovered blocks that
-- may themselves have transfer failures) and so the DiscoveryState is
-- updated with the new function; this is a *new* function so it
-- cannot continue to try to refine the existing function.
--
-- Also note that because the Discovery process has to be re-done from
-- scratch for a function each time there are new transfer solutions,
-- all *previous* transfer solutions for that function must also be
-- applied.
refineFunctions
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> MD.DiscoveryState arch
  -> Solutions arch -- ^ accumulated solutions so-far
  -> [Some (MD.DiscoveryFunInfo arch)]
  -> m (MD.DiscoveryState arch)
refineFunctions _   inpDS _ [] = pure inpDS
refineFunctions context inpDS solns (Some fi:fis) =
  refineTransfers context inpDS solns fi [] >>= \case
    Nothing -> refineFunctions context inpDS solns fis  -- case 1 or 2
    Just (updDS, solns') ->
      refineFunctions context updDS solns' $ allFuns updDS -- case 3


-- | This attempts to refine the passed in function.  There are three
-- cases:
--
--   1. The function has no unknown transfers: no refinement needed
--
--   2. An unknown transfer was refined successfully.  This resulted
--      in a new DiscoveryState, with a new Function (replacing the
--      old function).  The new Function may have new blocks that need
--      refinement, but because this is a new function the "current"
--      function cannot be refined anymore, so return 'Just' this
--      updated DiscoveryState.
--
--   3. The unknown transfer could not be refined: move to the next
--      block in this function with an unknown transfer target and
--      recursively attempt to resolve that one.
--
--   4. All unknown transfer blocks were unable to be refined: the
--   original function is sufficient.
refineTransfers
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> MD.DiscoveryState arch
  -> Solutions arch
  -> MD.DiscoveryFunInfo arch ids
  -> [RFU.BlockIdentifier arch ids]
  -> m (Maybe (MD.DiscoveryState arch, Solutions arch))
refineTransfers context inpDS solns fi failedRefines = do
  let unrefineable = flip elem failedRefines . RFU.blockID
      unkTransfers = filter (not . unrefineable) $ getUnknownTransfers fi
      thisUnkTransfer = head unkTransfers
      thisId = RFU.blockID thisUnkTransfer
  if null unkTransfers
  then return Nothing
  else refineBlockTransfer context inpDS solns fi thisUnkTransfer >>= \case
    Nothing    -> refineTransfers context inpDS solns fi (thisId : failedRefines)
    r@(Just _) -> return r


getUnknownTransfers :: MD.DiscoveryFunInfo arch ids
                    -> [MD.ParsedBlock arch ids]
getUnknownTransfers fi =
  filter isUnknownTransfer $ Map.elems $ fi ^. MD.parsedBlocks

isUnknownTransfer :: MD.ParsedBlock arch ids -> Bool
isUnknownTransfer pb =
  case MD.pblockTermStmt pb of
    MD.ClassifyFailure {} -> True
    _ -> False

-- | This function attempts to use an SMT solver to refine the block
-- transfer.  If the transfer can be resolved, it will update the
-- input DiscoveryState with the new block information (plus any
-- blocks newly discovered via the transfer resolution) and return
-- that.  If it was unable to refine the transfer, it will return
-- Nothing and this block will be added to the "unresolvable" list.
refineBlockTransfer
  :: ( MS.SymArchConstraints arch
     , 16 <= MC.ArchAddrWidth arch
     , MonadIO m
     , RSE.Refinement t solver fp
     )
  => RSE.RefinementContext arch t solver fp
  -> MD.DiscoveryState arch
  -> Solutions arch
  -> MD.DiscoveryFunInfo arch ids
  -> MD.ParsedBlock arch ids
  -> m (Maybe (MD.DiscoveryState arch, Solutions arch))
refineBlockTransfer context inpDS solns fi blk =
  case RP.pathTo (RFU.blockID blk) $ RP.buildFuncPath fi of
    Nothing -> error "unable to find function path for block" -- internal error
    Just p -> do soln <- refinePath context inpDS fi p (RP.pathDepth p) 1
                 case soln of
                   Nothing -> return Nothing
                   Just sl ->
                     -- The discovered solutions are sorted here for
                     -- convenience and test stability, but the
                     -- sorting is not otherwise required.
                     let solns' = Map.insert (MD.pblockAddr blk) (sort sl) solns
                         updDS = error "Update Discovery" -- updateDiscovery inpDS solns' fi
                     in return $ Just (updDS, solns')


{-
updateDiscovery :: ( MC.RegisterInfo (MC.ArchReg arch)
                   , KnownNat (MC.ArchAddrWidth arch)
                   , MC.ArchConstraints arch
                   ) =>
                   DiscoveryState arch
                -> Solutions arch
                -> DiscoveryFunInfo arch ids
                -> DiscoveryState arch
updateDiscovery inpDS solns finfo =
  let funAddr = discoveredFunAddr finfo
  in addDiscoveredFunctionBlockTargets inpDS funAddr $
     guideTargets solns

guideTargets :: ( MC.RegisterInfo (MC.ArchReg arch)
                , KnownNat (MC.ArchAddrWidth arch)
                , MC.ArchConstraints arch
                )=>
                Solutions arch -- ^ all rewrites to apply to this function's blocks
             -> BlockTermRewriter arch s src tgt
guideTargets solns addr tStmt = do
  case Map.lookup addr solns of
    Nothing -> pure tStmt
    Just soln -> rewriteTS tStmt soln
  where
    -- The existing TermStmt is assumed to be a TranslateError, and
    -- further assumed to be an unknown transfer because the
    -- equation for the final ip_reg could not be analyzed to obtain
    -- a simple static address.  The tgtAddrs is supplied via
    -- additional analysis (e.g. symbolic execution via SMT solver)
    -- and yielded one or more addresses to branch to.
    --
    -- The strategy here is to insert Blocks that explicitly set IP
    -- register to the target address(es) so that parseBlocks can
    -- identify those target jumps and also continue to explore those
    -- targets.
    rewriteTS old [] = pure old  -- no targets provided, cannot rewrite
    rewriteTS old (t:[]) = do
      -- The only TermStmt that allows Block insertion is the Branch,
      -- so it must be used even if there is only one address.  If
      -- there is only one address, the explicit setting of ip_reg is
      -- to the same value on both branches, so the condition for the
      -- branch is immaterial.
      j <- jumpToTarget (regsFrom old) t
      c <- RW.rewriteApp $ testIP (regsFrom old) t
      pure $ Branch c j j
    rewriteTS old (t:ts) = do
      c <- RW.rewriteApp $ testIP (regsFrom old) t
      j <- jumpToTarget (regsFrom old) t
      o <- RW.addNewBlockFromRewrite [] =<< rewriteTS old ts
      pure $ Branch c j o

    jumpToTarget inpRegs tgt = let nbt = FetchAndExecute newRegs
                                   newRegs = inpRegs & MC.curIP .~ addrAsValue tgt
                               in RW.addNewBlockFromRewrite [] nbt

    regsFrom = \case
      TranslateError regs _ -> regs
      FetchAndExecute regs  -> regs
      o -> error $ "Unexpected previous TermStmt: " <> show (PP.pretty o)

    addrAsValue a = case MC.segoffAsAbsoluteAddr a of
                      Just a' -> MC.bvValue $ fromIntegral a'
                      Nothing -> error "Unable to determine absolute address in guideTargets"

    testIP regs v = let ipAddr = regs^.MC.curIP
                        tgtVal = addrAsValue v
                    in MC.Eq ipAddr tgtVal
-}


refinePath :: ( MS.SymArchConstraints arch
              , 16 <= MC.ArchAddrWidth arch
              , MonadIO m
              , RSE.Refinement t solver fp
              )
           => RSE.RefinementContext arch t solver fp
           -> MD.DiscoveryState arch
           -> MD.DiscoveryFunInfo arch ids
           -> RP.FuncBlockPath arch ids
           -> Int
           -> Int
           -> m (Maybe (Solution arch))
refinePath context inpDS fi path maxlevel numlevels =
  let thispath = RP.takePath numlevels path
      smtEquation = equationFor inpDS fi thispath
  in solve context smtEquation >>= \case
       Nothing -> return Nothing -- divergent, stop here
       soln@(Just{}) -> if numlevels >= maxlevel
                          then return soln
                          else refinePath context inpDS fi path maxlevel (numlevels + 1)

data Equation arch ids = Equation (MD.DiscoveryState arch) [[MD.ParsedBlock arch ids]]
type Solution arch = [ArchSegmentOff arch]  -- identified transfers
type Solutions arch = Map.Map (ArchSegmentOff arch) (Solution arch)


equationFor :: MD.DiscoveryState arch
            -> MD.DiscoveryFunInfo arch ids
            -> RP.FuncBlockPath arch ids
            -> Equation arch ids
equationFor inpDS fi p =
  let pTrails = RP.pathForwardTrails p
      pTrailBlocks = map (RFU.getBlock fi) <$> pTrails
  in if and (any (not . isJust) <$> pTrailBlocks)
     then error "did not find requested block in discovery results!" -- internal
       else Equation inpDS (catMaybes <$> pTrailBlocks)

solve :: ( MS.SymArchConstraints arch
         , 16 <= MC.ArchAddrWidth arch
         , MonadIO m
         , RSE.Refinement t solver fp
         )
      => RSE.RefinementContext arch t solver fp
      -> Equation arch ids
      -> m (Maybe (Solution arch))
solve context (Equation inpDS paths) = do
  blockAddrs <- concat <$> forM paths
    (\path -> liftIO $ RSE.smtSolveTransfer context inpDS path)
  return $ if null blockAddrs then Nothing else Just blockAddrs

--isBetterSolution :: Solution arch -> Solution arch -> Bool
-- isBetterSolution :: [ArchSegmentOff arch] -> [ArchSegmentOff arch] -> Bool
-- isBetterSolution = (<)
