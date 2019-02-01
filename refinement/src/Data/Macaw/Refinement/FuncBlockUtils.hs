module Data.Macaw.Refinement.FuncBlockUtils
  ( BlockIdentifier
  , blockID
  , blockInFunction
  , blockTransferTo
  , funBlockIDs
  , funForBlock
  , getBlock
  )
where

import           Control.Lens
import qualified Data.Foldable as F
import           Data.Macaw.CFG.AssignRhs ( ArchSegmentOff )
import           Data.Macaw.Discovery.State ( DiscoveryFunInfo
                                            , DiscoveryState
                                            , ParsedBlock(..)
                                            , ParsedTermStmt(..)
                                            , funInfo
                                            , parsedBlocks
                                            , stmtsTerm
                                            )
import qualified Data.Map as Map
import           Data.Maybe ( isJust )
import           Data.Parameterized.Some
import           Data.Semigroup

import           Prelude


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

-- | Returns the actual block (if it exists) from the Discovery State
-- (in the first function for which it exists).
getBlock :: DiscoveryState arch
         -> BlockIdentifier arch
         -> Maybe (Some (ParsedBlock arch))
getBlock ds blkID =
  case filter (funIncludesBlock blkID) (ds ^. funInfo ^.. folded) of
    ((Some fi):_) -> Some <$> (fi ^. parsedBlocks) Map.!? blkID
    [] -> Nothing

-- | This function identifies the possible target addresses (of other
-- blocks within this function) from the terminal statement in the
-- input block.  Note that this function is responsible for returning
-- the under-approximation of target blocks *within* the current
-- function; it may return target addresses that lie outside of the
-- function, but it is not required to, nor will it return other
-- external targets.
blockTransferTo :: DiscoveryFunInfo arch ids
                -> BlockIdentifier arch
                -> [ArchSegmentOff arch]
blockTransferTo fi frm =
  let frmBlk = (fi ^. parsedBlocks) Map.!? frm
      lclTgtAddrs termStmt =
        case termStmt of
          ParsedCall _ mbTgt | Just tgt <- mbTgt -> [tgt]
                             | otherwise -> []
          ParsedJump _ tgt -> [tgt]
          ParsedLookupTable _ _ tgts -> F.toList tgts
          ParsedReturn {} -> []
          ParsedIte _ thenS elseS -> lclTgtAddrs (stmtsTerm thenS) <>
                                    lclTgtAddrs (stmtsTerm elseS)
          PLTStub _ tgt _ -> undefined -- KWQ tgt?
          ParsedArchTermStmt _ _ mbTgt | Just tgt <- mbTgt -> [tgt]
                                       | otherwise -> []
          ParsedTranslateError {} -> []
          ClassifyFailure {} -> []
          _ -> undefined
  in case frmBlk of
       Just fBlk -> lclTgtAddrs $ stmtsTerm $ blockStatementList fBlk
       Nothing -> error "block ID not valid" -- impossible
