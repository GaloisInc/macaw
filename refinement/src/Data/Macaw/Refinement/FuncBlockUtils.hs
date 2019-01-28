module Data.Macaw.Refinement.FuncBlockUtils
  ( BlockIdentifier
  , blockID
  , blockInFunction
  , blockTransferTo
  , funBlockIDs
  , funForBlock
  )
where

import           Control.Lens
import           Data.Macaw.CFG.AssignRhs ( ArchSegmentOff )
import           Data.Macaw.Discovery.State ( DiscoveryFunInfo
                                            , DiscoveryState
                                            , ParsedBlock(..)
                                            , funInfo
                                            , parsedBlocks
                                            , stmtsTerm
                                            )
import qualified Data.Map as Map
import           Data.Maybe ( isJust )
import           Data.Parameterized.Some


-- | The local type used to identify blocks.  Using a local
-- abstraction for this allows this code to be more independent of the
-- underlying block information.
type BlockIdentifier arch = ArchSegmentOff arch

-- | Obtain the local 'BlockIdentifier' value for a block.
blockID :: Some (ParsedBlock arch) -> BlockIdentifier arch
blockID = viewSome pblockAddr


-- | Return the ID's for all blocks in the function
funBlockIDs :: Some (DiscoveryFunInfo arch) -> [BlockIdentifier arch]
funBlockIDs (Some fi) = blockID . Some <$> Map.elems (fi ^. parsedBlocks)

-- | Given a block determine which function that block is a part of.
funForBlock :: Some (ParsedBlock arch)
            -> DiscoveryState arch
            -> Maybe (Some (DiscoveryFunInfo arch))
funForBlock pb ds =
  let blkID = blockID pb
      blkFuns = ds ^. funInfo ^.. folded . filtered (funIncludesBlock blkID)
  in case blkFuns of
       [Some f] -> Just $ Some f
       _ -> Nothing  -- should not be possible

blockInFunction :: DiscoveryFunInfo arch ids
              -> ArchSegmentOff arch
              -> Maybe (BlockIdentifier arch)
blockInFunction fi addr = blockID . Some <$> (fi ^. parsedBlocks) Map.!? addr

funIncludesBlock :: BlockIdentifier arch
                 -> Some (DiscoveryFunInfo arch)
                 -> Bool
funIncludesBlock blkID (Some fi) =
  isJust ((fi ^. parsedBlocks) Map.!? blkID)

blockTransferTo :: DiscoveryFunInfo arch ids -> BlockIdentifier arch -> ArchSegmentOff arch
blockTransferTo fi frm = let frmBlk = (fi ^. parsedBlocks) Map.!? frm
                         in case frmBlk of
                              Just fBlk -> case stmtsTerm $ blockStatementList fBlk of
                                             _ -> undefined
                              Nothing -> error "block ID not valid" -- impossible
