{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
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
  )
where

import           Control.Applicative
import           Control.Lens ( (^.) )
import qualified Data.Foldable as F
import qualified Data.Graph.Haggle as G
import qualified Data.Graph.Haggle.Algorithms.DFS as GD
import qualified Data.Map.Strict as M
import           Data.Macaw.CFG.AssignRhs ( ArchAddrWidth, ArchSegmentOff )
import           Data.Macaw.Discovery.State ( DiscoveryFunInfo )
import qualified Data.Macaw.Discovery.State as MDS
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.Memory ( MemWidth )
import           Data.Macaw.Refinement.FuncBlockUtils ( BlockIdentifier(..)
                                                      , blockInFunction
                                                      , blockTransferTo
                                                      , funBlockIDs
                                                      )
import qualified Data.Macaw.Refinement.FuncBlockUtils as FBU
import           Data.Maybe ( mapMaybe )
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc
import qualified Text.PrettyPrint.ANSI.Leijen as PP

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
                        }

emptyCFG :: DiscoveryFunInfo arch ids -> CFG arch ids
emptyCFG func = CFG { cfgFunc = func
                    , cfg = G.emptyGraph
                    , cfgEntry = entryID
                    , cfgVirtualRoots = [entryID]
                    , cfgNodeAddrs = M.empty
                    , cfgAddrNodes = M.empty
                    }
  where
    entryID = FBU.blockID entryBlock
    Just entryBlock = M.lookup (MDS.discoveredFunAddr func) (func ^. MDS.parsedBlocks)

-- | Build a 'CFG' from a 'DiscoveryFunInfo'
--
-- The CFG will include all of the blocks reachable from the entry point to the
-- function.  This CFG is slightly quirky, reflecting its use in this package:
-- there are no edges from blocks ending in calls to the return site.  The use
-- of this CFG is to ask what is definitely reachable via reverse DFS from a
-- particular point, but stopping at function entry and function calls.  We need
-- to stop at function calls because we do not currently prove that locals are
-- unaltered after a call.
mkPartialCFG :: (MemWidth (MC.ArchAddrWidth arch)) => DiscoveryFunInfo arch ids -> CFG arch ids
mkPartialCFG fi = F.foldl' buildCFG nodeGraph allBlocks
  where
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
        MDS.PLTStub {} -> gr
        MDS.ParsedArchTermStmt {} -> gr
        MDS.ParsedReturn {} -> gr
        MDS.ParsedTranslateError {} -> gr
        MDS.ClassifyFailure {} -> gr
        -- FIXME: Add in the branches in the side table of info

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

sliceComponents :: CFGSlice arch ids -> (MDS.ParsedBlock arch ids, [MDS.ParsedBlock arch ids], MDS.ParsedBlock arch ids)
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
cfgPathsTo :: (MemWidth (MC.ArchAddrWidth arch)) => FBU.BlockIdentifier arch ids -> CFG arch ids -> [CFGSlice arch ids]
cfgPathsTo targetBlockID g0 = mapMaybe slice (cfgVirtualRoots g0)
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

{-

Save the "virtual roots" of the graph:

- The entry point
- The successors to each call

let reach = RDFS target g
for each vRoot $ \r -> do
  let pathProjection = dfs vroot `intersect` reach

-}

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


instance ( MemWidth (ArchAddrWidth arch) ) =>
         Pretty (FuncBlockPath arch ids) where
  pretty (Path bid anc loop) =
    let label = [ pretty "Path", prettyBlkId bid
                , parens $ hsep [ pretty $ length anc, pretty " callers" ]
                ]
        looptxt = if null loop then []
                  else [parens (hsep [ pretty "loops from:"
                                     , list ( prettyBlkId <$> loop )])]
        prettyBlkId = pretty . show . PP.pretty . biArchSegmentOff
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
          -> ArchSegmentOff arch
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
