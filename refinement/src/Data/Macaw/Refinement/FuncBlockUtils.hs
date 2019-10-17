module Data.Macaw.Refinement.FuncBlockUtils
  ( BlockIdentifier(..)
  , blockID
  , blockInFunction
  , blockTransferTo
  , funBlockIDs
  , getBlock
  )
where

import           Control.Lens
import qualified Data.Foldable as F
import           Data.Macaw.CFG.AssignRhs ( ArchSegmentOff )
import           Data.Macaw.Discovery.State ( DiscoveryFunInfo
                                            , ParsedBlock(..)
                                            , ParsedTermStmt(..)
                                            , parsedBlocks
                                            )
import qualified Data.Map as Map
import           Data.Semigroup

import           Prelude


-- | The local type used to identify blocks.  Using a local
-- abstraction for this allows this code to be more independent of the
-- underlying block information.
newtype BlockIdentifier arch ids = BlockIdentifier
  { biArchSegmentOff :: ArchSegmentOff arch
  }
  deriving (Eq, Ord)

-- | Obtain the local 'BlockIdentifier' value for a block.
blockID :: ParsedBlock arch ids -> BlockIdentifier arch ids
blockID =  BlockIdentifier . pblockAddr


-- | Return the ID's for all blocks in the function
funBlockIDs :: DiscoveryFunInfo arch ids -> [BlockIdentifier arch ids]
funBlockIDs fi = map blockID $ Map.elems (fi ^. parsedBlocks)

blockInFunction :: DiscoveryFunInfo arch ids
                -> ArchSegmentOff arch
                -> Maybe (BlockIdentifier arch ids)
blockInFunction fi addr = blockID <$> (fi ^. parsedBlocks) Map.!? addr

-- | Returns the actual block (if it exists) from the Discovery State
-- (in the first function for which it exists).
getBlock :: DiscoveryFunInfo arch ids
         -> BlockIdentifier arch ids
         -> Maybe (ParsedBlock arch ids)
getBlock fi blkID = (fi ^. parsedBlocks) Map.!? biArchSegmentOff blkID

-- | This function identifies the possible target addresses (of other
-- blocks within this function) from the terminal statement in the
-- input block.  Note that this function is responsible for returning
-- the under-approximation of target blocks *within* the current
-- function; it may return target addresses that lie outside of the
-- function, but it is not required to, nor will it return other
-- external targets.
blockTransferTo :: DiscoveryFunInfo arch ids
                -> BlockIdentifier arch ids
                -> [ArchSegmentOff arch]
blockTransferTo fi blkID =
  let lclTgtAddrs termStmt =
        case termStmt of
          ParsedCall _ mbTgt | Just tgt <- mbTgt -> [tgt]
                             | otherwise -> []
          ParsedJump _ tgt -> [tgt]
          ParsedLookupTable _ _ tgts -> F.toList tgts
          ParsedReturn {} -> []
          ParsedBranch _ _ thenTgt elseTgt -> [thenTgt, elseTgt]
          PLTStub _ tgt _ -> undefined -- KWQ tgt?
          ParsedArchTermStmt _ _ mbTgt | Just tgt <- mbTgt -> [tgt]
                                       | otherwise -> []
          ParsedTranslateError {} -> []
          ClassifyFailure {} -> []
  in case getBlock fi blkID of
       Just fBlk -> lclTgtAddrs $ pblockTermStmt fBlk
       Nothing -> error "block ID not valid" -- impossible
