{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Refinement.Path
  ( FuncBlockPath(..)
  , buildFuncPath
  , pathDepth
  , pathForwardTrails
  , pathTo
  , takePath
  --  * CFG
  , CFG
  , mkPartialCFG
  , cfgPathsTo
  , CFGSlice
  , sliceComponents
  , sliceAddress
  )
where

import           Control.Applicative
import           Control.Lens ( (^.) )
import qualified Data.Foldable as F
import qualified Data.Graph.Haggle as G
import qualified Data.Graph.Haggle.Algorithms.DFS as GD
import qualified Data.Map.Strict as M
import           Data.Macaw.CFG.AssignRhs ( ArchAddrWidth )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.Discovery.State ( DiscoveryFunInfo )
import qualified Data.Macaw.Discovery.State as MDS
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Refinement.FuncBlockUtils ( BlockIdentifier(..)
                                                      , blockInFunction
                                                      , blockTransferTo
                                                      , funBlockIDs
                                                      )
import qualified Data.Macaw.Refinement.FuncBlockUtils as FBU
import           Data.Maybe ( fromMaybe, mapMaybe )
import qualified Data.Set as S
import           Prettyprinter

data CFG arch ids = CFG { cfgFunc  :: DiscoveryFunInfo arch ids
                        -- ^ The original function
                        , cfg      :: !(G.PatriciaTree (FBU.BlockIdentifier arch ids) ())
                        -- ^ The directed graph representing control flow
                        , cfgEntry :: FBU.BlockIdentifier arch ids
                        -- ^ The entry block of the CFG
                        , cfgVirtualRoots :: [FBU.BlockIdentifier arch ids]
                        -- ^ The disconnected roots that could reach targets (entry point + successors of function calls)
                        , cfgNodeAddrs :: !(M.Map G.Vertex (FBU.BlockIdentifier arch ids))
                        , cfgAddrNodes :: !(M.Map (FBU.BlockIdentifier arch ids) G.Vertex)
                        , cfgBackEdges :: !(M.Map (MC.ArchSegmentOff arch) (S.Set (MC.ArchSegmentOff arch)))
                        -- ^ Any back edges discovered in the CFG; we need this
                        -- so that we can break them before we send them off to
                        -- the SMT solver
                        }

emptyCFG :: DiscoveryFunInfo arch ids -> CFG arch ids
emptyCFG func = CFG { cfgFunc = func
                    , cfg = G.emptyGraph
                    , cfgEntry = entryID
                    , cfgVirtualRoots = [entryID]
                    , cfgNodeAddrs = M.empty
                    , cfgAddrNodes = M.empty
                    , cfgBackEdges = M.empty
                    }
  where
    entryID = FBU.blockID entryBlock
    Just entryBlock = M.lookup (MDS.discoveredFunAddr func) (func ^. MDS.parsedBlocks)

computeBackEdges :: forall arch ids . (MC.MemWidth (MC.ArchAddrWidth arch)) => CFG arch ids -> CFG arch ids
computeBackEdges cfg0 =
  cfg0 { cfgBackEdges = backEdgeMap }
  where
    g = cfg cfg0
    nodeToBlockId n =
      case M.lookup n (cfgNodeAddrs cfg0) of
        Nothing -> error ("Missing block identifier from vertex: " ++ show n)
        Just bid -> bid
    (backEdgeMap, _) = F.foldl' go (M.empty, S.empty) (cfgVirtualRoots cfg0)
    go :: (M.Map (MC.ArchSegmentOff arch) (S.Set (MC.ArchSegmentOff arch)), S.Set (MC.ArchSegmentOff arch))
       -> FBU.BlockIdentifier arch ids
       -> (M.Map (MC.ArchSegmentOff arch) (S.Set (MC.ArchSegmentOff arch)), S.Set (MC.ArchSegmentOff arch))
    go acc@(_, visited) blockId
      | S.member blockAddr visited = acc
      | otherwise =
         let addVisited (m, v) = (m, S.insert blockAddr v)
         in case MDS.pblockTermStmt block of
           MDS.ParsedCall _ Nothing -> addVisited acc
           MDS.ParsedCall _ (Just target) ->
             addTargetsIfBackedges blockId blockAddr (addVisited acc) [target]
           MDS.ParsedJump _ target ->
             addTargetsIfBackedges blockId blockAddr (addVisited acc) [target]
           MDS.ParsedBranch _ _ target1 target2 ->
             addTargetsIfBackedges blockId blockAddr (addVisited acc) [target1, target2]
           MDS.ParsedLookupTable _ _ targets ->
             addTargetsIfBackedges blockId blockAddr (addVisited acc) targets
           MDS.PLTStub _ retTarget _ ->
             addTargetsIfBackedges blockId blockAddr (addVisited acc) [retTarget]
           MDS.ParsedReturn {} -> addVisited acc
           MDS.ParsedArchTermStmt _ _ Nothing -> addVisited acc
           MDS.ParsedArchTermStmt _ _ (Just tgt) ->
             addTargetsIfBackedges blockId blockAddr (addVisited acc) [tgt]
           MDS.ParsedTranslateError {} -> addVisited acc
           MDS.ClassifyFailure {} ->
             let dfi = cfgFunc cfg0
                 resolutions = MDS.discoveredClassifyFailureResolutions dfi
                 refinementEdges = fromMaybe [] (lookup blockAddr resolutions)
             in addTargetsIfBackedges blockId blockAddr (addVisited acc) refinementEdges
      where
        blockAddr = FBU.biArchSegmentOff blockId
        block = case FBU.getBlock (cfgFunc cfg0) blockId of
          Nothing -> error ("Missing block label for node: " ++ show blockId)
          Just b -> b
    addTargetsIfBackedges :: (F.Foldable f)
                          => FBU.BlockIdentifier arch ids
                          -> MC.ArchSegmentOff arch
                          -> (M.Map (MC.ArchSegmentOff arch) (S.Set (MC.ArchSegmentOff arch)), S.Set (MC.ArchSegmentOff arch))
                          -> f (MC.ArchSegmentOff arch)
                          -> (M.Map (MC.ArchSegmentOff arch) (S.Set (MC.ArchSegmentOff arch)), S.Set (MC.ArchSegmentOff arch))
    addTargetsIfBackedges blockId blockAddr acc targets =
      let acc' = F.foldl' (addIfBackedge blockAddr) acc targets
          Just node = M.lookup blockId (cfgAddrNodes cfg0)
          succNodes = G.successors g node
      in F.foldl' go acc' (map nodeToBlockId succNodes)
    addIfBackedge blockAddr acc@(m, visited) target
      | S.member target visited = (M.insertWith S.union blockAddr (S.singleton target) m, visited)
      | otherwise = acc

-- | Build a 'CFG' from a 'DiscoveryFunInfo'
--
-- The CFG will include all of the blocks reachable from the entry point to the
-- function.  This CFG is slightly quirky, reflecting its use in this package:
-- there are no edges from blocks ending in calls to the return site.  The use
-- of this CFG is to ask what is definitely reachable via reverse DFS from a
-- particular point, but stopping at function entry and function calls.  We need
-- to stop at function calls because we do not currently prove that locals are
-- unaltered after a call.
mkPartialCFG :: (MC.MemWidth (MC.ArchAddrWidth arch)) => DiscoveryFunInfo arch ids -> CFG arch ids
mkPartialCFG fi = computeBackEdges graph
  where
    graph = F.foldl' buildCFG nodeGraph allBlocks
    allBlocks = M.toList (fi ^. MDS.parsedBlocks)
    -- We need to add all of the nodes to the graph first so that there are
    -- vertexes allocated for them
    nodeGraph = F.foldl' addNode (emptyCFG fi) allBlocks
    addNode gr (_addr, pb) =
      let bid = FBU.blockID pb
          (nodeId, g1) = G.insertLabeledVertex (cfg gr) bid
          nodeAddrs' = M.insert nodeId bid (cfgNodeAddrs gr)
          addrNodes' = M.insert bid nodeId (cfgAddrNodes gr)
      in gr { cfg = g1
            , cfgNodeAddrs = nodeAddrs'
            , cfgAddrNodes = addrNodes'
            }
    addEdge addrNodes srcId g0 tgtAddr =
      let Just tgtBlock = M.lookup tgtAddr (fi ^. MDS.parsedBlocks)
          Just tgtId = M.lookup (FBU.blockID tgtBlock) addrNodes
          Just (_e, g) = G.insertLabeledEdge g0 srcId tgtId ()
      in g
    buildCFG gr (_addr, pb) =
      let Just nodeId = M.lookup (FBU.blockID pb) (cfgAddrNodes gr)
      in case MDS.pblockTermStmt pb of
        MDS.ParsedJump _ tgt ->
          let g2 = addEdge (cfgAddrNodes gr) nodeId (cfg gr) tgt
          in gr { cfg = g2 }
        MDS.ParsedBranch _ _ tgt1 tgt2 ->
          let g2 = F.foldl' (addEdge (cfgAddrNodes gr) nodeId) (cfg gr) [tgt1, tgt2]
          in gr { cfg = g2 }
        MDS.ParsedLookupTable _ _ addrs ->
          let g2 = F.foldl' (addEdge (cfgAddrNodes gr) nodeId) (cfg gr) addrs
          in gr { cfg = g2 }
        MDS.ParsedCall _ (Just retAddr) ->
          let Just retBlock = FBU.blockInFunction fi retAddr
          in gr { cfgVirtualRoots = retBlock : cfgVirtualRoots gr
                }
        MDS.ParsedCall _ Nothing -> gr
        MDS.PLTStub _ retTgt _ ->
          let Just retBlock = FBU.blockInFunction fi retTgt
          in gr { cfgVirtualRoots = retBlock : cfgVirtualRoots gr
                }
        MDS.ParsedArchTermStmt _ _ Nothing -> gr
        MDS.ParsedArchTermStmt _ _ (Just tgt) ->
          let Just retBlock = FBU.blockInFunction fi tgt
          in gr { cfgVirtualRoots = retBlock : cfgVirtualRoots gr
                }
        MDS.ParsedReturn {} -> gr
        MDS.ParsedTranslateError {} -> gr
        MDS.ClassifyFailure {} ->
          let resolutions = MDS.discoveredClassifyFailureResolutions fi
              refinementEdges = fromMaybe [] (lookup (MDS.pblockAddr pb) resolutions)
              g2 = F.foldl' (addEdge (cfgAddrNodes gr) nodeId) (cfg gr) refinementEdges
          in gr { cfg = g2 }

-- | A contiguous slice from a CFG
--
-- Slices are contiguous sets of blocks connected by control flow.  They are not
-- necessarily linear.  The "body" does not contain the entry or target blocks
-- (to avoid duplication).
--
-- The entry and target could be the same (in which case the body is empty)
data CFGSlice arch ids =
  CFGSlice { sliceCFG :: CFG arch ids
           , sliceEntry :: MDS.ParsedBlock arch ids
           -- ^ The starting point of the slice
           , sliceBody :: [MDS.ParsedBlock arch ids]
           -- ^ Other blocks in the slice
           , sliceTarget :: MDS.ParsedBlock arch ids
           -- ^ The terminal block of the slice
           }

-- | The address of the block for which we created this slice (the target that has unresolved control flow)
sliceAddress :: CFGSlice arch ids -> MC.ArchSegmentOff arch
sliceAddress  = MDS.pblockAddr . sliceTarget

sliceComponents :: CFGSlice arch ids
                -> (MDS.ParsedBlock arch ids, [MDS.ParsedBlock arch ids], MDS.ParsedBlock arch ids)
sliceComponents slice = (sliceEntry slice, sliceBody slice, sliceTarget slice)

-- | Compute all of the blocks backward reachable from the given block address
--
-- This function returns a list of paths from some block to the target block.
-- There may be multiple paths because the backwards traversal stops at function
-- calls (which may split paths).
--
-- Note that paths are not necessarily linear and may contain branches.  They
-- are really contiguous CFG slices.  Each path may have "dangling" branches
-- that do not lead to the target block.
cfgPathsTo :: (MC.MemWidth (MC.ArchAddrWidth arch))
           => FBU.BlockIdentifier arch ids
           -> CFG arch ids
           -> [CFGSlice arch ids]
cfgPathsTo targetBlockID g0 =
  -- Note: before we return slices, we break any backedges that they contain.
  -- This will prevent us from resolving some cases that we may have been able
  -- to, but loops cause the symbolic execution engine to loop forever.
  --
  -- If we used the online backend, we could use pathsat checking to attempt to
  -- resolve some of them (under a timeout)
  map (breakBackedges g0) $ mapMaybe slice (cfgVirtualRoots g0)
  where
    Just targetNode = M.lookup targetBlockID (cfgAddrNodes g0)
    Just targetBlock = FBU.getBlock (cfgFunc g0) targetBlockID
    backwardReachable = S.fromList (GD.rdfs (cfg g0) [targetNode])
    slice root = do
      let Just startNode = M.lookup root (cfgAddrNodes g0)
      let forwardReachable = S.fromList (GD.dfs (cfg g0) [startNode])
      let common = S.intersection forwardReachable backwardReachable
      case S.null common of
        True -> Nothing
        False -> do
          let common' = S.delete targetNode $ S.delete startNode common
          let Just startBlock = FBU.getBlock (cfgFunc g0) root
          Just $ CFGSlice { sliceCFG = g0
                          , sliceEntry = startBlock
                          , sliceTarget = targetBlock
                          , sliceBody = map nodeToBlock (F.toList common')
                          }
    nodeToBlock n =
      let Just bid = M.lookup n (cfgNodeAddrs g0)
          Just pb = FBU.getBlock (cfgFunc g0) bid
      in pb

-- | Traverse a 'CFGSlice' and break any backedges by replacing jump targets
-- with invalid pointers.  Since there will not be blocks at these invalid
-- pointers, the conversion code in macaw-symbolic will assume that the branches
-- are not taken.
breakBackedges :: (MM.MemWidth (MC.ArchAddrWidth arch))
               => CFG arch ids
               -> CFGSlice arch ids
               -> CFGSlice arch ids
breakBackedges cfg0 slice =
  CFGSlice { sliceCFG = sliceCFG slice
           , sliceEntry = breakBlockBackedge (sliceEntry slice)
           , sliceBody = map breakBlockBackedge (sliceBody slice)
           , sliceTarget = breakBlockBackedge (sliceTarget slice)
           }
  where
    invalidTarget = mkInvalidAddress cfg0
    backedges = cfgBackEdges cfg0
    breakBlockBackedge blk =
      case M.lookup (MDS.pblockAddr blk) backedges of
        Nothing -> blk
        Just bes ->
          blk { MDS.pblockTermStmt = rewriteTerminator bes (MDS.pblockTermStmt blk)
              }
    rewriteTerminator backTargets t =
      case t of
        MDS.ParsedCall _ Nothing -> t
        MDS.ParsedCall regs (Just tgt) ->
          MDS.ParsedCall regs (Just (replaceTarget backTargets tgt))
        MDS.PLTStub regs tgt sym ->
          MDS.PLTStub regs (replaceTarget backTargets tgt) sym
        MDS.ParsedJump regs tgt ->
          MDS.ParsedJump regs (replaceTarget backTargets tgt)
        MDS.ParsedBranch regs cond t1 t2 ->
          MDS.ParsedBranch regs cond (replaceTarget backTargets t1) (replaceTarget backTargets t2)
        MDS.ParsedLookupTable regs val tgts ->
          MDS.ParsedLookupTable regs val (fmap (replaceTarget backTargets) tgts)
        MDS.ParsedReturn {} -> t
        MDS.ParsedArchTermStmt _ _ Nothing -> t
        MDS.ParsedArchTermStmt stmt regs (Just tgt) ->
          MDS.ParsedArchTermStmt stmt regs (Just (replaceTarget backTargets tgt))
        MDS.ParsedTranslateError {} -> t
        -- FIXME: This case needs to handle previously-discovered targets from
        -- refinement
        --
        -- The problem is that slices don't contain enough information to
        -- resolve previously-recovered branch targets.  We need to carry around
        -- the side map to enable it, as well as modify the macaw-symbolic entry
        -- point to respect it.
        MDS.ClassifyFailure {} -> t
    replaceTarget backTargets tgt
      | S.member tgt backTargets = invalidTarget
      | otherwise = tgt

-- | We need an invalid address to substitute for intra-procedural jump targets
-- that would introduce a backedge into the slice.
--
-- This function creates an invalid address by finding any address outside of
-- the function being analyzed.  It has to be a reasonably valid address since
-- it is a MemSegmentOffset - anything outside of the function is sufficient.
--
-- The first strategy is to use the address before the function, which will not
-- correspond to a block in the function (most of the time...)
--
-- The fallback is to try the address after.  This will fail for the smallest
-- binary that only contains the target function, which is not a terrible
-- outcome.
mkInvalidAddress :: (MM.MemWidth (MC.ArchAddrWidth arch))
                 => CFG arch ids
                 -> MM.MemSegmentOff (MC.ArchAddrWidth arch)
mkInvalidAddress cfg0 =
  case MM.incSegmentOff (MDS.discoveredFunAddr dfi) (-1) of
    Just addr -> addr
    Nothing -> F.foldl' maxBlockAddr (MDS.discoveredFunAddr dfi) (dfi ^. MDS.parsedBlocks)
  where
    dfi = cfgFunc cfg0
    maxBlockAddr addr b
      | Just postBlockAddr <- MDS.pblockAddr b `MM.incSegmentOff` fromIntegral (MDS.blockSize b + 1) =
          max addr postBlockAddr
      | otherwise = addr

-- | This is the datatype that represents the back-path of blocks in
-- the function from the exit point(s) to either the entry point or a
-- loop point.
data FuncBlockPath arch ids = Path (BlockIdentifier arch ids) [FuncBlockPath arch ids] [BlockIdentifier arch ids]
  -- (BlockIdentifier arch) -- ^ current block identifier
  -- [FuncBlockPath arch]   -- ^ next non-loop path elements (callees for
  --                        -- a ForwardPath, callers for a BackwardPath)
  -- [BlockIdentifier arch] -- ^ next elements which would form a path
  --                        -- loop.

deriving instance (MC.MemWidth (MC.RegAddrWidth (MC.ArchReg arch))) => Show (FuncBlockPath arch ids)


instance ( MC.MemWidth (ArchAddrWidth arch) ) =>
         Pretty (FuncBlockPath arch ids) where
  pretty (Path bid anc loop) =
    let label = [ pretty "Path", prettyBlkId bid
                , parens $ hsep [ pretty $ length anc, pretty " callers" ]
                ]
        looptxt = if null loop then []
                  else [parens (hsep [ pretty "loops from:"
                                     , list ( prettyBlkId <$> loop )])]
        prettyBlkId = pretty . biArchSegmentOff
    in vsep [ hsep (label <> looptxt)
            , nest 4 $ vsep (pretty <$> anc)
            ]


-- | Builds a list of all the back-paths through the specific
-- function.  The returned list is a list of all the exit points of
-- the function, with a FuncBlockPath tree indicating the blocks
-- forming the path to that exit point.
--
-- A function exit point usually represents a RET or JMP, or an ite of
-- JMP targets; at the present time it is assumed that the latter
-- targets cannot be a mix of function-internal and function-external
-- targets.
buildFuncPath :: DiscoveryFunInfo arch ids -> [FuncBlockPath arch ids]
buildFuncPath fi =
  let blks = funBlockIDs fi
  in fst $ bldFPath fi ([], blks)


-- Internal function to build a FuncBlockPath from an input
-- BlockIdentifer array.  This recursively processes elements,
-- migrating them from the tuple snd to the tuple fst; the final
-- result should have an empty second array, and the elements in the
-- first array are all the exit points from the function.  Each
-- recursive invocation takes the next BlockIdentifier and adds it to
-- an existing path or starts a new path for that BlockIdentifier.
bldFPath :: DiscoveryFunInfo arch ids
         -> ([FuncBlockPath arch ids], [BlockIdentifier arch ids])
         -> ([FuncBlockPath arch ids], [BlockIdentifier arch ids])
bldFPath _fi x@(_, []) = x
bldFPath fi (fs, b:bs) =
  let nextBlkAddrs = blockTransferTo fi b
      isPathElemForBlock bid (Path pid _ _) = bid == pid
      isTopLevelPathEntry = not $ null $ filter (isPathElemForBlock b) fs
      updPath = if null nextBlkAddrs
                then if isTopLevelPathEntry
                     then fs
                     else Path b [] [] : fs
                else foldr (bldFPath' fi b) fs nextBlkAddrs
  in bldFPath fi (updPath, bs)


bldFPath' :: DiscoveryFunInfo arch ids
          -> BlockIdentifier arch ids
          -> MC.ArchSegmentOff arch
          -> [FuncBlockPath arch ids]
          -> [FuncBlockPath arch ids]
bldFPath' fi b nextAddr fs =
  let nextBlkID = blockInFunction fi nextAddr

      isPathElemForBlock bid (Path pid _ _) = bid == pid
      isTopLevelPathEntry e = not $ null $ filter (isPathElemForBlock e) fs

      -- until an if "ancestor" is attached to any callees it appears
      -- to be a terminal path point.  When a callee is identified,
      -- this ancestor should be removed from the terminal list and
      -- added to the callee location, but any path information
      -- gathered for the ancestor should be preserved when doing
      -- that.
      ancPathElem = case filter (isPathElemForBlock b) fs of
                      (a : []) -> Just a
                      _ -> Nothing

      ancToAdd = maybe (Path b [] []) id ancPathElem

      addAncToExisting _ [] = (False, [])
      addAncToExisting cb (ph@(Path tbid anc loop):ps) =
        if tbid == cb
        then (True, Path tbid (ancToAdd:anc) loop : ps)
        else let (e, p) = addAncToExisting cb ps in (e, ph : p)

      addAncestor cb p =
        let (toExisting, updPath) = addAncToExisting cb p
        in if toExisting
           then case ancPathElem of
                  Nothing -> updPath
                  Just _ -> filter (not . isPathElemForBlock b) updPath -- remove terminal entry
           else if isTopLevelPathEntry cb
                then p
                else Path cb [Path b [] []] [] : p  -- new terminal entry

  in case nextBlkID of
       Nothing -> fs -- target addr was external to this function; ignore it
       Just cb -> addAncestor cb fs


-- | Given a function's call paths, return the subset of the call
-- paths that terminates with the specified block.  The specified
-- block might be reachable backward from several exit points, but the
-- inbound paths (i.e. above/forward to) the specified block must be
-- the same for all outbound paths (loops are elided).
pathTo :: BlockIdentifier arch ids
       -> [FuncBlockPath arch ids]
       -> Maybe (FuncBlockPath arch ids)
pathTo blkID (p@(Path i anc _):ps) =
  if blkID == i
  then Just p
  else let depth = pathTo blkID anc
           breadth = pathTo blkID ps
       in breadth <|> depth
pathTo _ [] = Nothing


-- | Returns the first n levels (callers) for the specified Block path
-- in the Function.
takePath :: Int -> FuncBlockPath arch ids -> FuncBlockPath arch ids
takePath n (Path blkid anc loop) =
  if n > 0
  then Path blkid (takePath (n-1) <$> anc) loop
  else Path blkid [] loop


-- | Returns the maximum length (depth) of all paths through the
-- function (ignoring loops)
pathDepth :: FuncBlockPath arch ids -> Int
pathDepth (Path _ [] _) = 0
pathDepth (Path _ anc _) = 1 + maximum (pathDepth <$> anc)


-- | Converts a Path tree into a list of the distinct paths, where
-- each path is represented by a list of block IDs in the order that
-- they would be executed (i.e. the back-path is converted to a
-- forward-chain list.
--
-- For example:
--
-- > Path 1
-- >   [ Path 2 [ Path 3 ] []
-- >   , Path 4 [ Path 5 [ Path 6 [] []
-- >                     , Path 7 [ Path 3 [] []] []
-- >                     ] []
-- >            ] []
-- >   ] []
--
-- Is converted to:
--
-- >  [ [ 3, 2, 1 ]
-- >  , [ 6, 5, 4, 1 ]
-- >  , [ 3, 7, 5, 4, 1 ]
-- >  ]
--
pathForwardTrails :: FuncBlockPath arch ids -> [ [BlockIdentifier arch ids] ]
pathForwardTrails (Path i [] _) = [[i]]
pathForwardTrails (Path i anc _) = let ft = concatMap pathForwardTrails anc
                                       appendTo v l = l <> [v]
                                   in map (appendTo i) ft
