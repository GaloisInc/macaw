{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Refinement.Path
  ( FuncBlockPath
  , buildFuncPath
  , pathDepth
  , pathTo
  , takePath
  )
where

import           Control.Applicative
import           Data.Macaw.CFG.AssignRhs ( ArchAddrWidth, ArchSegmentOff )
import           Data.Macaw.Discovery.State ( DiscoveryFunInfo )
import           Data.Macaw.Memory ( MemWidth )
import           Data.Macaw.Refinement.FuncBlockUtils ( BlockIdentifier
                                                      , blockInFunction
                                                      , blockTransferTo
                                                      , funBlockIDs
                                                      )
import           Data.Parameterized.Some
import           Data.Text.Prettyprint.Doc
import qualified Text.PrettyPrint.ANSI.Leijen as PP


-- | This is the datatype that represents the back-path of blocks in
-- the function from the exit point(s) to either the entry point or a
-- loop point.
data FuncBlockPath arch =
  Path
  (BlockIdentifier arch) -- current block
  [FuncBlockPath arch] -- ancestors to this block (non-loop)
  [BlockIdentifier arch] -- previously seen ancestors (loop)


instance ( MemWidth (ArchAddrWidth arch) ) =>
         Pretty (FuncBlockPath arch) where
  pretty (Path bid anc loop) =
    let label = [ pretty "Path", prettyBlkId bid
                , parens $ hsep [ pretty $ length anc, pretty " callers" ]
                ]
        looptxt = if null loop then []
                  else [parens (hsep [ pretty "loops from:"
                                     , list ( prettyBlkId <$> loop )])]
        prettyBlkId = pretty . show . PP.pretty
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
buildFuncPath :: Some (DiscoveryFunInfo arch) -> [FuncBlockPath arch]
buildFuncPath sfi@(Some fi) =
  let blks = funBlockIDs sfi
  in fst $ bldFPath fi ([], blks)


-- Internal function to build a FuncBlockPath from an input
-- BlockIdentifer array.  This recursively processes elements,
-- migrating them from the tuple snd to the tuple fst; the final
-- result should have an empty second array, and the elements in the
-- first array are all the exit points from the function.  Each
-- recursive invocation takes the next BlockIdentifier and adds it to
-- an existing path or starts a new path for that BlockIdentifier.
bldFPath :: DiscoveryFunInfo arch ids
         -> ([FuncBlockPath arch], [BlockIdentifier arch])
         -> ([FuncBlockPath arch], [BlockIdentifier arch])
bldFPath _fi x@(_, []) = x
bldFPath fi (fs, b:bs) =
  let nextBlkAddrs = blockTransferTo fi b
      updPath = foldr (bldFPath' fi b) fs nextBlkAddrs
  in bldFPath fi (updPath, bs)


bldFPath' :: DiscoveryFunInfo arch ids
          -> BlockIdentifier arch
          -> ArchSegmentOff arch
          -> [FuncBlockPath arch]
          -> [FuncBlockPath arch]
bldFPath' fi b nextAddr fs =
  let nextBlkID = blockInFunction fi nextAddr

      isPathElemForBlock bid (Path pid _ _) = bid == pid

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
           else Path b [] [] : p  -- new terminal entry

  in case nextBlkID of
       Nothing -> fs -- should never happen (block not in function)
       Just cb -> addAncestor cb fs


-- | Given a function's call paths, return the subset of the call
-- paths that terminates with the specified block.  The specified
-- block might be reachable backward from several exit points, but the
-- inbound paths (i.e. above/forward to) the specified block must be
-- the same for all outbound paths (loops are elided).
pathTo :: BlockIdentifier arch -> [FuncBlockPath arch] -> Maybe (FuncBlockPath arch)
pathTo blkID (p@(Path i anc _):ps) =
  if blkID == i
  then Just p
  else let depth = pathTo blkID anc
           breadth = pathTo blkID ps
       in breadth <|> depth
pathTo _ [] = Nothing


-- | Returns the first n levels (callers) for the specified Block path
-- in the Function.
takePath :: Int -> FuncBlockPath arch -> FuncBlockPath arch
takePath n (Path blkid anc loop) =
  if n > 0
  then Path blkid (takePath (n-1) <$> anc) loop
  else Path blkid [] loop


-- | Returns the maximum length (depth) of all paths through the
-- function (ignoring loops)
pathDepth :: FuncBlockPath arch -> Int
pathDepth (Path _ [] _) = 0
pathDepth (Path _ anc _) = 1 + maximum (pathDepth <$> anc)
