module Data.Macaw.Refinement.FuncBlockUtils
  ( BlockIdentifier(..)
  , blockID
  , blockInFunction
  , blockTransferTo
  , funBlockIDs
  , getBlock
  )
where

import           Control.Lens ( (^.) )
import qualified Data.Foldable as F
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery.State as MDS
import qualified Data.Map as Map

import           Prelude


-- | The local type used to identify blocks.  Using a local
-- abstraction for this allows this code to be more independent of the
-- underlying block information.
newtype BlockIdentifier arch ids = BlockIdentifier
  { biArchSegmentOff :: MC.ArchSegmentOff arch
  }
  deriving (Eq, Ord)

-- | Obtain the local 'BlockIdentifier' value for a block.
blockID :: MDS.ParsedBlock arch ids -> BlockIdentifier arch ids
blockID =  BlockIdentifier . MDS.pblockAddr


-- | Return the ID's for all blocks in the function
funBlockIDs :: MDS.DiscoveryFunInfo arch ids -> [BlockIdentifier arch ids]
funBlockIDs fi = map blockID $ Map.elems (fi ^. MDS.parsedBlocks)

blockInFunction :: MDS.DiscoveryFunInfo arch ids
                -> MC.ArchSegmentOff arch
                -> Maybe (BlockIdentifier arch ids)
blockInFunction fi addr = blockID <$> (fi ^. MDS.parsedBlocks) Map.!? addr

-- | Returns the actual block (if it exists) from the Discovery State
-- (in the first function for which it exists).
getBlock :: MDS.DiscoveryFunInfo arch ids
         -> BlockIdentifier arch ids
         -> Maybe (MDS.ParsedBlock arch ids)
getBlock fi blkID = (fi ^. MDS.parsedBlocks) Map.!? biArchSegmentOff blkID

-- | This function identifies the possible target addresses (of other
-- blocks within this function) from the terminal statement in the
-- input block.  Note that this function is responsible for returning
-- the under-approximation of target blocks *within* the current
-- function; it may return target addresses that lie outside of the
-- function, but it is not required to, nor will it return other
-- external targets.
blockTransferTo :: MDS.DiscoveryFunInfo arch ids
                -> BlockIdentifier arch ids
                -> [MC.ArchSegmentOff arch]
blockTransferTo fi blkID =
  let lclTgtAddrs termStmt =
        case termStmt of
          MDS.ParsedCall _ mbTgt | Just tgt <- mbTgt -> [tgt]
                             | otherwise -> []
          MDS.ParsedJump _ tgt -> [tgt]
          MDS.ParsedLookupTable _ _ tgts -> F.toList tgts
          MDS.ParsedReturn {} -> []
          MDS.ParsedBranch _regs _cond trueTarget falseTarget -> [ trueTarget, falseTarget ]
          MDS.PLTStub _ tgt _ ->
            -- PLT stubs are really calls and jump outside of the function (but
            -- will return). We should be able to return no targets here.
            []
          MDS.ParsedArchTermStmt _ _ mbTgt | Just tgt <- mbTgt -> [tgt]
                                       | otherwise -> []
          MDS.ParsedTranslateError {} -> []
          MDS.ClassifyFailure {} -> []
  in case getBlock fi blkID of
       Just fBlk -> lclTgtAddrs $ MDS.pblockTermStmt fBlk -- stmtsTerm $ blockStatementList fBlk
       Nothing -> error "block ID not valid" -- impossible
