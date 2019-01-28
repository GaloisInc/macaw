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
import           Data.Macaw.CFG.AssignRhs ( ArchAddrWidth )
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
buildFuncPath :: Some (DiscoveryFunInfo arch) -> [FuncBlockPath arch]
buildFuncPath sfi@(Some fi) =
  let blks = funBlockIDs sfi
  in fst $ bldFPath fi ([], blks)


bldFPath :: DiscoveryFunInfo arch ids
         -> ([FuncBlockPath arch], [BlockIdentifier arch])
         -> ([FuncBlockPath arch], [BlockIdentifier arch])
bldFPath _fi x@(_, []) = x
bldFPath fi (fs, b:_) = ([Path b [] []], [])

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
