{-# LANGUAGE FlexibleContexts #-}
module Summary (
  Summary(..)
  , summarizeInfo
  , blockAddresses
  ) where

import           Control.Lens ( (^.) )
import qualified Control.Lens as L
import qualified Data.Foldable as F
import qualified Data.Map as M
import           Data.Maybe ( catMaybes, isNothing )
import           Data.Monoid
import           Data.Parameterized.Some ( Some(..) )
import           Data.Semigroup
import qualified Data.Set as S
import           Data.Text.Prettyprint.Doc as PP
import           Data.Word ( Word64 )

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM

import           Prelude

data Summary = Summary { functionCnt :: !Int
                       , functionsWithErrors :: !Int
                       , blockCnt :: !Int
                       , blockTranslateErrors :: !Int
                       , blockUnknownTargetErrors :: !Int
                       -- ^ Number of ClassifyFailure terminators
                       , maxBlocksPerFunction :: !Int
                       }

instance Semigroup Summary where
  a <> b =
    Summary { functionCnt = functionCnt a + functionCnt b
            , functionsWithErrors = functionsWithErrors a + functionsWithErrors b
            , blockCnt = blockCnt a + blockCnt b
            , blockTranslateErrors = blockTranslateErrors a + blockTranslateErrors b
            , blockUnknownTargetErrors = blockUnknownTargetErrors a + blockUnknownTargetErrors b
            , maxBlocksPerFunction = max (maxBlocksPerFunction a) (maxBlocksPerFunction b)
            }

instance Monoid Summary where
  mempty = Summary 0 0 0 0 0 0

instance PP.Pretty Summary where
  pretty s = PP.vcat $ catMaybes
    [ Just $ PP.pretty ":: Function count =" <+> PP.pretty (show $ functionCnt s)
    , if functionsWithErrors s > 0
      then Just $ PP.pretty "::    with errors =" <+> PP.pretty (show $ functionsWithErrors s)
      else Nothing
    , Just $ PP.pretty ":: Total block count =" <+> PP.pretty (show $ blockCnt s)
    , Just $ PP.pretty ":: Max blocks/function =" <+> PP.pretty (show $ maxBlocksPerFunction s)
    , if blockTranslateErrors s > 0
      then Just (PP.pretty "::  blocks with Translate errors (disassembly) =" <+>
                 PP.pretty (show $ blockTranslateErrors s))
      else Nothing
    , if blockUnknownTargetErrors s > 0
      then Just (PP.pretty "::  blocks with Classification/Unknown Target errors (discovery) =" <+>
                 PP.pretty (show $ blockUnknownTargetErrors s))
      else Nothing
    ]

summarizeBlock :: MD.DiscoveryFunInfo arch ids
               -> Summary
               -> (a, MD.ParsedBlock arch ids)
               -> Summary
summarizeBlock dfi s (_, pblk) =
  case MD.pblockTermStmt pblk of
    MD.ParsedTranslateError {} ->
      s { blockTranslateErrors = blockTranslateErrors s + 1 }
    MD.ClassifyFailure {}
      | isNothing (lookup (MD.pblockAddr pblk) (MD.discoveredClassifyFailureResolutions dfi)) ->
        s { blockUnknownTargetErrors = blockUnknownTargetErrors s + 1 }
    _ -> s

summarizeFunction :: Summary
                  -> (a, Some (MD.DiscoveryFunInfo arch))
                  -> Summary
summarizeFunction s (_funAddr, Some dfi) =
  (mappend s blksSummary) { functionsWithErrors = functionsWithErrors s + funcErrs }
  where
    blks = dfi ^. MD.parsedBlocks . L.to M.toList
    numBlks = length blks
    blksSummary = F.foldl' (summarizeBlock dfi) initFuncSummary blks
    initFuncSummary = mempty { functionCnt = 1
                             , blockCnt = numBlks
                             , maxBlocksPerFunction = numBlks
                             }
    funcErrs = F.foldl' (\v f -> f blksSummary + v) 0 [ blockTranslateErrors, blockUnknownTargetErrors ]

summarizeInfo :: MD.DiscoveryState arch -> Summary
summarizeInfo dstate = F.foldl' summarizeFunction mempty (dstate ^. MD.funInfo . L.to M.toList)

-- | Compute a map from function addresses to the addresses of their blocks
--
-- We use Word64 here for easy interop with the test suite since Word64 is big
-- enough for all pointers right now
blockAddresses :: (MM.MemWidth (MC.ArchAddrWidth arch)) => MD.DiscoveryState arch -> M.Map Word64 (S.Set Word64)
blockAddresses dstate = F.foldl' addFunction M.empty (dstate ^. MD.funInfo . L.to M.toList)
  where
    addFunction m (funcAddr, Some dfi) =
      let blockAddrs = dfi ^. MD.parsedBlocks . L.to M.keys
          addrSet = S.fromList (fmap asWord64 blockAddrs)
      in M.insert (asWord64 funcAddr) addrSet m
    asWord64 addr =
      let Just mw = MM.segoffAsAbsoluteAddr addr
      in fromIntegral mw
