{- |

This module defines a relational abstract domain for tracking bounds
checks emitted by the compiler on registers and stack location.  This is
built on top of an underlying stack pointer tracking domain so that we
can include checks on stack locations and maintain constraints between
known equivalent values.

-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.AbsDomain.JumpBounds
  ( -- * Initial jump bounds
    InitJumpBounds
  , initBndsMap
  , functionStartBounds
  , ppInitJumpBounds
  , joinInitialBounds
    -- * IntraJumpbounds
  , IntraJumpBounds
  , blockEndBounds
  , postCallBounds
  , postJumpBounds
  , BranchBounds(..)
  , postBranchBounds
  , unsignedUpperBound
  -- * Jump Targets
  , IntraJumpTarget
  ) where

import           Control.Monad (unless, when)
import           Data.Bits
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Monoid
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Pair
import           Numeric.Natural
import           Prettyprinter

import           Data.Macaw.AbsDomain.AbsState ( AbsBlockState )
import           Data.Macaw.AbsDomain.CallParams
import           Data.Macaw.AbsDomain.StackAnalysis
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import           Data.Macaw.Types hiding (Type)
import           Data.Macaw.Utils.Changed

------------------------------------------------------------------------
-- RangePred

-- | A lower and or upper bound on a value when the value is interpreted
-- as an unsigned integer.
data RangePred u =
  -- | @RangePred w l h@ indicates a constraint on @w@ bits of the value
  -- are between @l@ and @h@ when the bitvector is treated as an
  -- unsigned integer.
  RangePred { rangeWidth :: !(NatRepr u)
            , rangeLowerBound :: !Natural
            , rangeUpperBound :: !Natural
            }
  deriving (Show)

mkLowerBound :: NatRepr u -> Natural -> RangePred u
mkLowerBound w l = RangePred w l (fromInteger (maxUnsigned w))

mkUpperBound :: NatRepr u -> Natural -> RangePred u
mkUpperBound w u = RangePred w 0 u

mkRangeBound :: NatRepr u -> Natural -> Natural -> RangePred u
mkRangeBound w l u = RangePred w l u

-- | Return true if range does not include whole domain.
rangeNotTotal :: RangePred u -> Bool
rangeNotTotal r = 0 < l || u < fromInteger (maxUnsigned w)
  where w = rangeWidth r
        l = rangeLowerBound r
        u = rangeUpperBound r

instance Pretty (RangePred u) where
  pretty (RangePred w l h) =
    parens (hsep [pretty (intValue w), pretty (toInteger l), pretty (toInteger h)])

------------------------------------------------------------------------
-- MaybeRangePred

-- | This describes a constraint associated with an equivalence class
-- of registers in @InitJumpBounds@.
--
-- The first parameter is the number of bits in the
data MaybeRangePred tp where
  -- | Predicate on bounds.
  SomeRangePred :: (u <= v)
                => !(RangePred u)
                -> MaybeRangePred (BVType v)
  -- | No constraints on value.
  NoRangePred :: MaybeRangePred tp

------------------------------------------------------------------------
-- InitJumpBounds

-- | Constraints on start of block
type BlockStartRangePred arch = LocMap (ArchReg arch) SubRange

-- | Bounds for a function as the start of a block.
data InitJumpBounds arch
   = InitJumpBounds { initBndsMap    :: !(BlockStartStackConstraints arch)
                    , initRngPredMap :: !(BlockStartRangePred arch)
                    , initAddrPredMap :: !(Map (MemAddr (ArchAddrWidth arch)) (MemVal SubRange))
                    }

-- | Pretty print jump bounds.
ppInitJumpBounds :: forall arch ann . ShowF (ArchReg arch) => InitJumpBounds arch -> [Doc ann]
ppInitJumpBounds cns
  =  ppBlockStartStackConstraints (initBndsMap cns)
  <> ppLocMap ppSubRange (initRngPredMap cns)
  <> [ ppSubRange (pretty a) r | (a,MemVal _repr r) <- Map.toList (initAddrPredMap cns) ]

instance ShowF (ArchReg arch) => Pretty (InitJumpBounds arch) where
  pretty = vcat . ppInitJumpBounds

instance ShowF (ArchReg arch) => Show (InitJumpBounds arch) where
  show = show . pretty

-- | Bounds at start of function.
functionStartBounds :: RegisterInfo (ArchReg arch) => InitJumpBounds arch
functionStartBounds =
  InitJumpBounds { initBndsMap = fnEntryBlockStartStackConstraints
                 , initRngPredMap = locMapEmpty
                 , initAddrPredMap = Map.empty
                 }

-- | Return a jump bounds that implies both input bounds, or `Nothing`
-- if every fact in the old bounds is implied by the new bounds.
joinInitialBounds :: forall arch
                  .  ( MemWidth (ArchAddrWidth arch)
                     , OrdF (ArchReg arch)
                     , HasRepr (ArchReg arch) TypeRepr
                     )
                  => InitJumpBounds arch
                  -> InitJumpBounds arch
                  -> Maybe (InitJumpBounds arch)
joinInitialBounds old new = runChanged $ do
  (finalStkCns, _) <- joinBlockStartStackConstraints (initBndsMap old) (initBndsMap new)
  unless (locMapNull (initRngPredMap old) && Map.null (initAddrPredMap old)) $ markChanged True
  pure $! InitJumpBounds { initBndsMap = finalStkCns
                         , initRngPredMap = locMapEmpty
                         , initAddrPredMap = Map.empty
                         }

------------------------------------------------------------------------
-- IntraJumpBounds

-- | This tracks bounds on a block during execution.
data IntraJumpBounds arch ids
   = IntraJumpBounds { intraInitBounds :: !(InitJumpBounds arch)
                     , intraStackConstraints :: !(BlockIntraStackConstraints arch ids)
                     , intraReadPredMap :: !(MapF (AssignId ids) SubRange)
                       -- ^ Map from assignments (that are memory
                       -- reads) and any range predicate inferred on
                       -- that access.
                       --
                       -- Used so we can eagerly compute range predicate.
                     , intraMemCleared :: !Bool
                       -- ^ Flag to indicate if we had any memory
                       -- writes in block that could have altered
                       -- invariants on non-stack memory accesses.
                     }

-- | Create index bounds from initial index bounds.
mkIntraJumpBounds :: forall arch ids
                  .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> IntraJumpBounds arch ids
mkIntraJumpBounds bnds =
  IntraJumpBounds { intraInitBounds = bnds
                  , intraStackConstraints = mkBlockIntraStackConstraints (initBndsMap bnds)
                  , intraReadPredMap = MapF.empty
                  , intraMemCleared = False
                  }

instance ShowF (ArchReg arch) => Pretty (IntraJumpBounds arch ids) where
  pretty cns = vcat $
    ppBlockStartStackConstraints (biscInitConstraints (intraStackConstraints cns))

-- | Update the stack constraints in the bounds.
modifyIntraStackConstraints ::IntraJumpBounds arch ids
                           ->  (BlockIntraStackConstraints arch ids -> BlockIntraStackConstraints arch ids)
                           -> IntraJumpBounds arch ids
modifyIntraStackConstraints bnds f = bnds { intraStackConstraints = f (intraStackConstraints bnds) }

discardMemBounds :: IntraJumpBounds arch ids -> IntraJumpBounds arch ids
discardMemBounds bnds =
  bnds { intraStackConstraints = discardMemInfo (intraStackConstraints bnds)
       , intraMemCleared = True
       }

------------------------------------------------------------------------
-- Execute a statement

-- | Function that determines whether it thinks an
-- architecture-specific function could modify stack.
--
-- Uses principal that architecture-specific functions can only depend
-- on value if they reference it in their foldable instance.
archFnCouldAffectStack :: forall f arch ids tp
                       .  (FoldableFC f, MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                       => BlockIntraStackConstraints arch ids
                       -> f (Value arch ids) tp
                       -> Bool
archFnCouldAffectStack cns = getAny . foldMapFC (Any . refStack)
  where refStack :: Value arch ids utp -> Bool
        refStack v =
          case intraStackValueExpr cns v of
            StackOffsetExpr _ -> True
            _ -> False

-- | Given a statement this modifies the bounds based on the statement.
execStatement :: ( MemWidth (ArchAddrWidth arch)
                 , OrdF (ArchReg arch)
                 , ShowF (ArchReg arch)
                 , FoldableFC (ArchFn arch)
                 )
              => IntraJumpBounds arch ids
              -> Stmt arch ids
              -> IntraJumpBounds arch ids
execStatement bnds stmt =
  case stmt of
    AssignStmt (Assignment aid arhs) -> do
      let bnds1 = case arhs of
                    ReadMem addrVal readRepr
                      | False <- intraMemCleared bnds
                      , Just addr <- valueAsMemAddr addrVal
                      , Just (MemVal bndRepr bnd)  <- Map.lookup addr (initAddrPredMap (intraInitBounds bnds))
                      , Just Refl <- testEquality readRepr bndRepr ->
                        bnds { intraReadPredMap = MapF.insert aid bnd (intraReadPredMap bnds) }
                    -- Clear all knowledge about the stack on architecture-specific
                    -- functions that accept stack pointer as they may have side effects.
                    --
                    -- Note. This is very conservative, and we may need to improve
                    -- this.
                    EvalArchFn f _ ->
                      if archFnCouldAffectStack (intraStackConstraints bnds) f then
                        discardMemBounds bnds
                       else
                        bnds { intraMemCleared = True }
                    _ -> bnds
      -- Associate the given expression with a bounds.
       in modifyIntraStackConstraints bnds1 $ \cns ->
                    intraStackSetAssignId aid (intraStackRhsExpr cns aid arhs) cns
    WriteMem addr repr val ->
      case intraStackValueExpr (intraStackConstraints bnds) addr of
        StackOffsetExpr addrOff ->
          modifyIntraStackConstraints bnds $ \cns ->
            writeStackOff cns addrOff repr val
        -- If we write to something other than stack, then clear all
        -- stack references.
        --
        -- This is probably not a good idea in general, but seems fine
        -- for stack detection.
        _ -> discardMemBounds bnds
    CondWriteMem{} -> discardMemBounds bnds
    InstructionStart{} -> bnds
    Comment{} -> bnds
    ExecArchStmt{} -> discardMemBounds bnds
    ArchState{} -> bnds

-- | Create bounds for end of block.
blockEndBounds :: ( MemWidth (ArchAddrWidth arch)
                  , OrdF (ArchReg arch)
                  , ShowF (ArchReg arch)
                  , FoldableFC (ArchFn arch)
                  )
               => InitJumpBounds arch
               -> [Stmt arch ids] -- ^
               -> IntraJumpBounds arch ids
blockEndBounds blockBnds stmts =
   foldl' execStatement (mkIntraJumpBounds blockBnds) stmts

------------------------------------------------------------------------
-- Operations

-- | Bounds for a function as the start of a block.
data ExprRangePredInfo arch ids =
  ExprRangePredInfo { erpiBndsMap    :: !(BlockStartStackConstraints arch)
                    , erpiRngPredMap :: !(BlockStartRangePred arch)
                    , erpiReadPredMap ::  !(MapF (AssignId ids) SubRange)
                    , erpiBranchConstraints :: !(BranchConstraints arch ids)
                    }

-- | This returns the current predicate on the bound expression.
exprRangePred :: ( MemWidth (ArchAddrWidth arch)
                 , HasRepr (ArchReg arch) TypeRepr
                 , OrdF (ArchReg arch)
                 , ShowF (ArchReg arch)
                 )
              => ExprRangePredInfo arch ids
              -> StackExpr arch ids tp
              -> MaybeRangePred tp
exprRangePred info e = do
  let brCns = erpiBranchConstraints info
  case e of
    ClassRepExpr loc ->
      case MapF.lookup loc (newClassRepConstraints brCns) of
        Just (SubRange r) -> SomeRangePred r
        Nothing ->
          case locLookup loc (erpiRngPredMap info) of
            Nothing ->  NoRangePred
            Just (SubRange r) -> SomeRangePred r
    UninterpAssignExpr aid _
      -- Lookup range predicate in newly asserted conditions
      | Just (SubRange r) <-  MapF.lookup aid (newUninterpAssignConstraints brCns)
      , rangeNotTotal r ->
        SomeRangePred r
      -- Otherwise lookup range predicate for memory reads from block start
      | Just (SubRange r) <- MapF.lookup aid (erpiReadPredMap info)
      , rangeNotTotal r -> do
          SomeRangePred r
      | otherwise ->
        NoRangePred
    StackOffsetExpr _ -> NoRangePred
    CExpr (BVCValue w i) -> SomeRangePred (mkRangeBound w (fromInteger i) (fromInteger i))
    CExpr _ -> NoRangePred
    AppExpr n _app
      -- If a bound has been deliberately asserted to this assignment
      -- then use that.
      | Just (SubRange r) <- MapF.lookup n (newUninterpAssignConstraints brCns)
      , rangeNotTotal r ->
          SomeRangePred r
    -- Otherwise see what we can infer.
    UExtExpr x w ->
      case exprRangePred info x of
        NoRangePred -> SomeRangePred (mkRangeBound w 0 (fromInteger (maxUnsigned w)))
        SomeRangePred r ->
          -- If bound covers all the bits in x, then we can extend it to all
          -- the bits in result (since new bits are false)
          --
          -- Otherwise, we only have the partial bound
          if leqF (typeWidth x) (rangeWidth r) then
            SomeRangePred (mkRangeBound w (rangeLowerBound r) (rangeUpperBound r))
           else
            -- Dynamic check on range width that should never fail.
            case testLeq (rangeWidth r) w of
              Just LeqProof -> SomeRangePred r
              Nothing -> error "exprRangePred given malformed app."
    AppExpr _n app ->
      case app of
        UExt x w
          | SomeRangePred r <- exprRangePred info x ->
              -- If bound covers all the bits in x, then we can extend it to all
              -- the bits in result (since new bits are false)
              --
              -- Otherwise, we only have the partial bound
              case testEquality (rangeWidth r) (typeWidth x) of
                Just Refl ->
                  SomeRangePred (mkRangeBound w (rangeLowerBound r) (rangeUpperBound r))
                Nothing ->
                  -- Dynamic check on range width that should never fail.
                  case testLeq (rangeWidth r) w of
                    Just LeqProof -> SomeRangePred r
                    Nothing -> error "exprRangePred given malformed app."
        BVAdd _ x (CExpr (BVCValue _ c))
          | SomeRangePred r <- exprRangePred info x
          , w <- rangeWidth r
          , lr <- rangeLowerBound r + fromInteger (toUnsigned w c)
          , ur <- rangeUpperBound r + fromInteger (toUnsigned w c)
          , lr `shiftR` fromIntegral (natValue w) == ur `shiftR` fromIntegral (natValue w)
          , lr' <- fromInteger (toUnsigned w (toInteger lr))
          , ur' <- fromInteger (toUnsigned w (toInteger ur)) ->
            SomeRangePred (RangePred w lr' ur')
        Trunc x w
          | SomeRangePred r <- exprRangePred info x
            -- Compare the range constraint with the output number of bits.
            -- If the bound on r covers at most the truncated number
            -- of bits, then we just pass it through.
          , Just LeqProof <- testLeq (rangeWidth r) w ->
            SomeRangePred r
        _ -> NoRangePred

-- | This returns a natural number with a computed upper bound for the
-- value or `Nothing` if no explicit bound was inferred.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => IntraJumpBounds arch ids
                   -> Value arch ids tp
                   -> Maybe Natural
unsignedUpperBound bnds v = do
  let ibnds = intraInitBounds bnds
  let stkCns = intraStackConstraints bnds
  let valExpr = intraStackValueExpr stkCns v
  let info =   ExprRangePredInfo { erpiBndsMap      =  biscInitConstraints stkCns
                                 , erpiRngPredMap   = initRngPredMap ibnds
                                 , erpiReadPredMap  = intraReadPredMap bnds
                                 , erpiBranchConstraints = emptyBranchConstraints
                                 }
  case exprRangePred info valExpr of
    SomeRangePred r -> do
      Refl <- testEquality (rangeWidth r) (typeWidth v)
      pure (rangeUpperBound r)
    NoRangePred -> Nothing

------------------------------------------------------------------------
-- SubRange

-- | This indicates a range predicate on a selected number of bits.
data SubRange tp where
  SubRange :: (u <= w) => !(RangePred u) -> SubRange (BVType w)

instance Pretty (SubRange tp) where
  pretty (SubRange p) = pretty p

ppSubRange :: Doc ann -> SubRange tp -> Doc ann
ppSubRange d (SubRange r) = d <+> "in" <+> pretty r

-- | Take the union of two subranges, and return `Nothing` if this is
-- a maximum range bound.
disjoinRangePred :: RangePred u -> RangePred u -> Maybe (RangePred u)
disjoinRangePred x y
    | l > 0 || h < fromInteger (maxUnsigned w) = Just (mkRangeBound w l h)
    | otherwise = Nothing
  where w = rangeWidth x
        l = min (rangeLowerBound x) (rangeLowerBound y)
        h = max (rangeUpperBound x) (rangeUpperBound y)

-- | Take the union of two subranges.
--
-- Return `Nothing` if range is not value.
disjoinSubRange :: SubRange tp -> SubRange tp -> Maybe (SubRange tp)
disjoinSubRange (SubRange x) (SubRange y)
  | Just Refl <- testEquality (rangeWidth x) (rangeWidth y) =
      SubRange <$> disjoinRangePred x y
  | otherwise =
      Nothing

------------------------------------------------------------------------
-- BranchConstraints

-- | Constraints on variable ranges inferred from a branch.
--
-- Branches predicates are analyzed to infer the constraints in
-- indices used in jump tables only, and this analysis is based on
-- that.
data BranchConstraints arch ids = BranchConstraints
  { newClassRepConstraints :: !(MapF (BoundLoc (ArchReg arch)) SubRange)
    -- ^ Maps locations to constraints on the initial values of
    -- the variable that are inferred from asserted branches.
  , newUninterpAssignConstraints :: !(MapF (AssignId ids) SubRange)
    -- ^ Maps assignments to inferred subrange constraints on
    -- assignments.
  , newAddrConstraints :: !(Map (MemAddr (ArchAddrWidth arch)) (MemVal SubRange))
    -- ^ Maps addresses to an inferred subrange constraints on the
    -- value stored at that address.
  }

instance ShowF (ArchReg arch) => Pretty (BranchConstraints arch ids) where
  pretty x =
    let cl = MapF.toList (newClassRepConstraints x)
        al = MapF.toList (newUninterpAssignConstraints x)
        ppLoc :: Pair (BoundLoc (ArchReg arch)) SubRange -> Doc ann
        ppLoc (Pair l r) = prettyF l <+> ":=" <+> pretty r
        ppAssign :: Pair (AssignId ids) SubRange -> Doc ann
        ppAssign (Pair l r) = ppAssignId l <+> ":=" <+> pretty r
     in vcat (fmap ppLoc cl ++ fmap ppAssign al)

instance ShowF (ArchReg arch) => Show (BranchConstraints arch ids) where
  show x = show (pretty x)

-- | Empty set of branch constraints.
emptyBranchConstraints :: BranchConstraints arch ids
emptyBranchConstraints =
  BranchConstraints { newClassRepConstraints = MapF.empty
                    , newUninterpAssignConstraints = MapF.empty
                    , newAddrConstraints = Map.empty
                    }

branchLocRangePred :: (u <= w)
                   => BoundLoc (ArchReg arch) (BVType w)
                   -> RangePred u
                   -> BranchConstraints arch ids
branchLocRangePred l p =
  BranchConstraints { newClassRepConstraints = MapF.singleton l (SubRange p)
                    , newUninterpAssignConstraints = MapF.empty
                    , newAddrConstraints = Map.empty
                    }

branchAssignRangePred :: (u <= w)
                      => AssignId ids (BVType w)
                      -> RangePred u
                      -> BranchConstraints arch ids
branchAssignRangePred a p =
  BranchConstraints { newClassRepConstraints = MapF.empty
                    , newUninterpAssignConstraints = MapF.singleton a (SubRange p)
                    , newAddrConstraints = Map.empty
                    }

-- | Create a predicate on a
branchReadMemRangePred :: (u <= w)
                       => AssignId ids (BVType w)
                       -> MemAddr (ArchAddrWidth arch)
                       -> MemRepr (BVType w)
                       -> RangePred u
                       -> BranchConstraints arch ids
branchReadMemRangePred aid a r p =
  BranchConstraints { newClassRepConstraints = MapF.empty
                    , newUninterpAssignConstraints = MapF.singleton aid (SubRange p)
                    , newAddrConstraints = Map.singleton a (MemVal r (SubRange p))
                    }

-- | @conjoinBranchConstraints x y@ returns constraints inferred from
-- by @x@ and @y@.
conjoinBranchConstraints :: OrdF (ArchReg arch)
                         => BranchConstraints arch ids
                         -> BranchConstraints arch ids
                         -> BranchConstraints arch ids
conjoinBranchConstraints x y = do
  BranchConstraints { newClassRepConstraints =
                        MapF.union (newClassRepConstraints x) (newClassRepConstraints y)
                    , newUninterpAssignConstraints =
                        MapF.union (newUninterpAssignConstraints x) (newUninterpAssignConstraints y)
                    , newAddrConstraints = Map.union (newAddrConstraints x) (newAddrConstraints y)
                    }

mapIntersectWithKeyMaybe :: Ord k
                         => (k -> a -> b -> Maybe c)
                         -> Map k a
                         -> Map k b
                         -> Map k c
mapIntersectWithKeyMaybe f =
  Map.mergeWithKey f (const Map.empty) (const Map.empty)

-- | @disjoinBranchConstraints x y@ returns constraints inferred that
-- @x@ or @y@ is true.
disjoinBranchConstraints :: (OrdF (ArchReg arch), ShowF (ArchReg arch))
                         => BranchConstraints arch ids
                         -> BranchConstraints arch ids
                         -> BranchConstraints arch ids
disjoinBranchConstraints x y =
  let joinMemVal :: k -> MemVal SubRange -> MemVal SubRange -> Maybe (MemVal SubRange)
      joinMemVal _ (MemVal rx sx) (MemVal ry sy) = do
        Refl <- testEquality rx ry
        MemVal rx <$> disjoinSubRange sx sy
   in BranchConstraints
      { newClassRepConstraints =
          MapF.intersectWithKeyMaybe
            (\_ -> disjoinSubRange)
            (newClassRepConstraints x)
            (newClassRepConstraints y)
      , newUninterpAssignConstraints =
          MapF.intersectWithKeyMaybe
            (\_ -> disjoinSubRange)
            (newUninterpAssignConstraints x)
            (newUninterpAssignConstraints y)
      , newAddrConstraints =
          mapIntersectWithKeyMaybe joinMemVal (newAddrConstraints x) (newAddrConstraints y)
      }

------------------------------------------------------------------------
-- Bounds inference

-- | @addRangePred v p@ asserts that @(trunc v (rangeWidth p))@ is satisifies
-- bounds in @p@.
--
-- In several architectures, but particularly x86, we may have
-- constraints on just the bits in an expression, and so our bounds
-- tracking has special support for this.
--
-- This either returns the refined bounds, or `Left msg` where `msg`
-- is an explanation of what inconsistency was detected.  The upper
-- bounds must be non-negative.
addRangePred :: ( MapF.OrdF (ArchReg arch)
                , HasRepr (ArchReg arch) TypeRepr
                , u <= w
                , MemWidth (ArchAddrWidth arch)
                , ShowF (ArchReg arch)
                )
               => BlockIntraStackConstraints arch ids
               -> StackExpr arch ids (BVType w)
                 -- ^ Value we are adding bounds for.
               -> RangePred u
                  -- ^ Predicate on value to assert.
               -> Either String (BranchConstraints arch ids)
addRangePred _ v rng
    -- Do nothing if upper bounds equals or exceeds maximum unsigned
    -- value.
  | bnd <- rangeUpperBound rng
  , bnd >= fromInteger (maxUnsigned (typeWidth v)) =
      Right emptyBranchConstraints
addRangePred _ v rng
    -- Do nothing if upper bounds equals or exceeds maximum unsigned
    -- value.
  | bnd <- rangeUpperBound rng
  , bnd >= fromInteger (maxUnsigned (typeWidth v)) =
      Right emptyBranchConstraints
addRangePred cns v p =
  case v of
    ClassRepExpr loc ->
      pure $! branchLocRangePred loc p
    UninterpAssignExpr aid (ReadMem addrVal r) | Just addr <- valueAsMemAddr addrVal ->
      pure $! branchReadMemRangePred aid addr r p
    UninterpAssignExpr aid _ ->
      pure $! branchAssignRangePred aid p
    -- Drop constraints on the offset of a stack.
    -- This is unexpected.
    StackOffsetExpr _i ->
      pure $! emptyBranchConstraints

    CExpr cv ->
      case cv of
        BVCValue _ c -> do
          when (toUnsigned (rangeWidth p) c > toInteger (rangeUpperBound p)) $ do
            Left "Constant is greater than asserted bounds."
          pure $! emptyBranchConstraints
        RelocatableCValue{} ->
          pure $! emptyBranchConstraints
        SymbolCValue{} ->
          pure $! emptyBranchConstraints
    UExtExpr x _outWidth
      -- If this constraint affects fewer bits than the extension,
      -- then we just propagate the property to value
      -- pre-extension.
      | Just LeqProof <- testLeq (rangeWidth p) (typeWidth x) ->
          addRangePred cns x p
      -- Otherwise, we still can constrain our width.
      | otherwise -> do
          addRangePred cns x (p { rangeWidth = typeWidth x })
    AppExpr n a ->
      case a of
        BVAdd _ x (CExpr (BVCValue w c))
          | RangePred _wp l u <- p
          , l' <- toInteger l - c
          , u' <- toInteger u - c
            -- Check overflow is consistent
          , l' `shiftR` fromIntegral (natValue w) == u' `shiftR` fromIntegral (natValue w) -> do
              addRangePred cns x (RangePred w (fromInteger (toUnsigned w l'))
                                              (fromInteger (toUnsigned w u')))

        -- Truncation passes through as we aonly affect low order bits.
        Trunc x _w ->
          case testLeq (rangeWidth p) (typeWidth x) of
            Just LeqProof ->
              addRangePred cns x p
            Nothing -> error "Invariant broken"

        -- If none of the above cases apply, then we just assign the
        -- predicate to the nonce identifing the app.
        _ ->
          Right $ branchAssignRangePred n p

-- | Assert a predicate is true/false and update bounds.
--
-- If it returns a new upper bounds, then that may be used.
-- Otherwise, it detects an inconsistency and returns a message
-- explaing why.
assertPred :: ( OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              , MemWidth (ArchAddrWidth arch)
              , ShowF (ArchReg arch)
              )
           => IntraJumpBounds arch ids
           -> Value arch ids BoolType -- ^ Value representing predicate
           -> Bool -- ^ Controls whether predicate is true or false
           -> Either String (BranchConstraints arch ids)
assertPred bnds (AssignedValue a) isTrue = do
  let cns = intraStackConstraints bnds
  case assignRhs a of
    EvalApp (Eq x (BVValue w c)) -> do
      addRangePred cns (intraStackValueExpr cns x)
                       (mkRangeBound w (fromInteger c) (fromInteger c))
    EvalApp (Eq (BVValue w c) x) -> do
      addRangePred cns (intraStackValueExpr cns x)
                   (mkRangeBound w (fromInteger c) (fromInteger c))
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c)) -> do
      if isTrue then do
        when (c == 0) $ Left "x < 0 must be false."
        addRangePred cns (intraStackValueExpr cns x)  $!
          mkUpperBound (typeWidth x) (fromInteger (c-1))
       else do
        addRangePred cns (intraStackValueExpr cns x)  $!
          mkLowerBound (typeWidth x) (fromInteger c)
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue w c) y) -> do
      p <-
        if isTrue then do
          when (c >= maxUnsigned w) $  Left "x <= max_unsigned must be true"
          pure $! mkLowerBound w (fromInteger (c+1))
         else do
          pure $! mkUpperBound w (fromInteger c)
      addRangePred cns (intraStackValueExpr cns y) p
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue w c)) -> do
      p <-
        if isTrue then
          pure $! mkUpperBound w (fromInteger c)
         else do
          when (c >= maxUnsigned w) $  Left "x <= max_unsigned must be true"
          pure $! mkLowerBound w (fromInteger (c+1))
      addRangePred cns (intraStackValueExpr cns x) p
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y)
      | isTrue -> do
          addRangePred cns (intraStackValueExpr cns y)
                       (mkLowerBound (typeWidth y) (fromInteger c))
      | otherwise -> do
          when (c == 0) $ Left "0 <= x cannot be false"
          addRangePred cns
            (intraStackValueExpr cns y)
            (mkUpperBound (typeWidth y) (fromInteger (c-1)))
    EvalApp (AndApp l r) ->
      if isTrue then
        conjoinBranchConstraints
          <$> assertPred bnds l True
          <*> assertPred bnds r True
      else
        disjoinBranchConstraints
          <$> assertPred bnds l False
          <*> assertPred bnds r False
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) ->
      if isTrue then
        -- Assert l | r
        disjoinBranchConstraints
          <$> assertPred bnds l True
          <*> assertPred bnds r True
      else
        -- Assert not l && not r
        conjoinBranchConstraints
          <$> assertPred bnds l False
          <*> assertPred bnds r False
    EvalApp (NotApp p) ->
      assertPred bnds p (not isTrue)
    _ -> Right emptyBranchConstraints
assertPred _ _ _ =
  Right emptyBranchConstraints

updateRangePredMap :: ( MemWidth (ArchAddrWidth arch)
                      , HasRepr (ArchReg arch) TypeRepr
                      , OrdF (ArchReg arch)
                      , ShowF (ArchReg arch)
                      )
                   => ExprRangePredInfo arch ids
                   -- ^ Information for computing range predicates of stack expressions.
                   -> LocMap (ArchReg arch) SubRange
                   -> Pair (BoundLoc (ArchReg arch)) (StackExpr arch ids)
                   -> LocMap (ArchReg arch) SubRange
updateRangePredMap info m (Pair l e) =
  case exprRangePred info e of
    SomeRangePred r -> nonOverlapLocInsert l (SubRange r) m
    NoRangePred -> m

nextStackConstraintsAndReps :: RegisterInfo (ArchReg arch)
                            => BlockIntraStackConstraints arch ids
                              -- ^ Bounds at end of this state.
                            -> RegState (ArchReg arch) (Value arch ids)
                            -- ^ Register values at start of next state.
                            -- Note. ip_reg is ignored
                            -> ( BlockStartStackConstraints arch
                               , [Pair (BoundLoc (ArchReg arch)) (StackExpr arch ids)]
                               )
nextStackConstraintsAndReps cns regs = runNextStateMonad $
  (,) <$> postJumpStackConstraints cns regs
      <*> getNextStateRepresentatives

-- | Bounds for block after jump
nextBlockBounds :: forall arch ids
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids
                   -- ^ Bounds at end of this state.
                -> BranchConstraints arch ids
                   -- ^ Constraints inferred from branch (or `emptyBranchConstraints)
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                   --
                   -- Note. This ignores @ip_reg@.
                -> InitJumpBounds arch
nextBlockBounds bnds brCns regs =
  let cns = intraStackConstraints bnds
      (stkCns, reps) = nextStackConstraintsAndReps cns regs
      info = ExprRangePredInfo { erpiBndsMap = biscInitConstraints cns
                               , erpiRngPredMap = locMapEmpty
                               , erpiReadPredMap = intraReadPredMap bnds
                               , erpiBranchConstraints = brCns
                               }
   in InitJumpBounds { initBndsMap     = stkCns
                     , initRngPredMap  = foldl' (updateRangePredMap info) locMapEmpty reps
                     , initAddrPredMap = newAddrConstraints brCns
                     }

-- | Bounds for block after jump
postJumpBounds :: forall arch ids
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids
                   -- ^ Bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitJumpBounds arch
postJumpBounds cns regs = nextBlockBounds cns emptyBranchConstraints regs

data BranchBounds arch
   = InfeasibleBranch
   | TrueFeasibleBranch  !(InitJumpBounds arch)
   | FalseFeasibleBranch !(InitJumpBounds arch)
   | BothFeasibleBranch  !(InitJumpBounds arch) !(InitJumpBounds arch)

postBranchBounds :: RegisterInfo (ArchReg arch)
                 => IntraJumpBounds arch ids -- ^ Bounds just before jump
                 -> RegState (ArchReg arch) (Value arch ids)
                 -- ^ Register values at start of next state.
                 -> Value arch ids BoolType -- ^ Branch condition
                 -> BranchBounds arch
postBranchBounds cns regs c = do
  case (assertPred cns c True, assertPred cns c False) of
    (Right brCnsT, Right brCnsF) ->
      BothFeasibleBranch (nextBlockBounds cns brCnsT regs)
                         (nextBlockBounds cns brCnsF regs)
    (Right brCnsT, Left _) ->
      TrueFeasibleBranch  (nextBlockBounds cns brCnsT regs)
    (Left _, Right brCnsF) ->
      FalseFeasibleBranch (nextBlockBounds cns brCnsF regs)
    (Left _, Left _) ->
      InfeasibleBranch

-- | Return the index bounds after a function call.
postCallBounds :: forall arch ids
               .  RegisterInfo (ArchReg arch)
               => CallParams (ArchReg arch)
               -> IntraJumpBounds arch ids
               -> RegState (ArchReg arch) (Value arch ids)
               -> InitJumpBounds arch
postCallBounds params cns regs =
  let cns' = runNextStateMonad $
              postCallStackConstraints params (intraStackConstraints cns) regs
   in InitJumpBounds { initBndsMap = cns'
                     , initRngPredMap = locMapEmpty
                     , initAddrPredMap = Map.empty
                     }

-- | This type is used to represent the location to return to *within a
-- function* after executing an architecture-specific terminator instruction.
--
--  * The 'MemSegmentOff' is the address to jump to next (within the function)
--  * The 'AbsBlockState' is the abstract state to use at the start of the block returned to (reflecting any changes made by the architecture-specific terminator)
--  * The 'Jmp.InitJumpBounds' is a collection of relations between values in registers and on the stack that should hold (see 'Jmp.postCallBounds' for to construct this in the common case)
--
-- Note: This is defined here (despite not being used here) to avoid import cycles elsewhere
type IntraJumpTarget arch =
  (ArchSegmentOff arch, AbsBlockState (ArchReg arch), InitJumpBounds arch)
