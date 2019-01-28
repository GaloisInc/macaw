module Data.Macaw.Refinement.Path
  ( FuncBlockPath
  , buildFuncPath
  , pathDepth
  , takePath
  )
where

import Data.Macaw.Discovery.State ( DiscoveryFunInfo )
import Data.Macaw.Refinement.FuncBlockUtils ( BlockIdentifier, funBlockIDs, blockTransferTo )
import Data.Parameterized.Some


data FuncBlockPath arch =
  Path
  (BlockIdentifier arch) -- current block
  [FuncBlockPath arch] -- ancestors to this block (non-loop)
  [BlockIdentifier arch] -- previously seen ancestors (loop)

buildFuncPath :: Some (DiscoveryFunInfo arch) -> FuncBlockPath arch
buildFuncPath sfi@(Some fi) =
  let blks = funBlockIDs sfi
  in case fst $ bldFPath fi ([], blks) of
       [fp] -> fp
       _ -> error "Non-singular function path"

bldFPath :: DiscoveryFunInfo arch ids
         -> ([FuncBlockPath arch], [BlockIdentifier arch])
         -> ([FuncBlockPath arch], [BlockIdentifier arch])
bldFPath _fi x@(_, []) = x
bldFPath fi (fs, b:_) = ([Path b [] []], [])

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
