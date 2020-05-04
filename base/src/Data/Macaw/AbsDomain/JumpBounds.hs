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
  , mkIntraJumpBounds
  , execStatement
  , postCallBounds
  , postJumpBounds
  , postBranchBounds
  , unsignedUpperBound
  ) where

import           Control.Monad.Reader
import           Data.Bits
import qualified Data.BitVector.Sized as BV
import           Data.Foldable
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Pair
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

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

mkLowerBound :: NatRepr u -> Natural -> RangePred u
mkLowerBound w l = RangePred w l (fromInteger (maxUnsigned w))

mkUpperBound :: NatRepr u -> Natural -> RangePred u
mkUpperBound w u = RangePred w 0 u

mkRangeBound :: NatRepr u -> Natural -> Natural -> RangePred u
mkRangeBound w l u = RangePred w l u

instance Pretty (RangePred u) where
  pretty (RangePred w l h) =
    parens (hsep [pretty (intValue w), pretty (toInteger l), pretty (toInteger h)])

------------------------------------------------------------------------
-- MaybeRangePred

-- | This describes a constraint associated with an equivalence class
-- of registers in @InitJumpBounds@.
--
-- The first parameter is the number of bits in the
data JustRangePred tp where
  -- | Predicate on bounds.
  JustRangePred :: (u <= v)
                => !(RangePred u)
                -> JustRangePred (BVType v)

ppJustRangePred :: Doc -> JustRangePred tp -> Doc
ppJustRangePred d (JustRangePred r) = d <+> text "in" <+> pretty r

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
type BlockStartRangePred arch = LocMap (ArchReg arch) JustRangePred

-- | Bounds for a function as the start of a block.
data InitJumpBounds arch
   = InitJumpBounds { initBndsMap    :: !(BlockStartStackConstraints arch)
                    , initRngPredMap :: !(BlockStartRangePred arch)
                    }

-- | Pretty print jump bounds.
ppInitJumpBounds :: forall arch . ShowF (ArchReg arch) => InitJumpBounds arch -> [Doc]
ppInitJumpBounds cns
  = ppBlockStartStackConstraints (initBndsMap cns)
  ++ ppLocMap ppJustRangePred (initRngPredMap cns)

instance ShowF (ArchReg arch) => Pretty (InitJumpBounds arch) where
  pretty = vcat . ppInitJumpBounds

instance ShowF (ArchReg arch) => Show (InitJumpBounds arch) where
  show = show . pretty

-- | Bounds at start of function.
functionStartBounds :: RegisterInfo (ArchReg arch) => InitJumpBounds arch
functionStartBounds =
  InitJumpBounds { initBndsMap = fnEntryBlockStartStackConstraints
                 , initRngPredMap = locMapEmpty
                 }

-- | Return a jump bounds that implies both input bounds, or `Nothing`
-- if every fact inx the old bounds is implied by the new bounds.
joinInitialBounds :: forall arch
                  .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> InitJumpBounds arch
                  -> Maybe (InitJumpBounds arch)
joinInitialBounds old new = runChanged $ do
  (finalStkCns, _) <- joinBlockStartStackConstraints (initBndsMap old) (initBndsMap new)
  pure $! InitJumpBounds { initBndsMap = finalStkCns
                         , initRngPredMap = locMapEmpty
                         }

------------------------------------------------------------------------
-- IntraJumpBounds

-- | Information about bounds for a particular value within a block.
data IntraJumpBounds arch ids
   = IntraJumpBounds { intraStackConstraints :: !(BlockIntraStackConstraints arch ids)
                     , intraRangePredMap :: !(BlockStartRangePred arch)
                     }


-- | Create index bounds from initial index bounds.
mkIntraJumpBounds :: forall arch ids
                  .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> IntraJumpBounds arch ids
mkIntraJumpBounds cns =
  IntraJumpBounds { intraStackConstraints = mkBlockIntraStackConstraints (initBndsMap cns)
                  , intraRangePredMap = initRngPredMap cns
                  }

initJumpBounds :: IntraJumpBounds arch ids -> InitJumpBounds arch
initJumpBounds cns =
  InitJumpBounds { initBndsMap = biscInitConstraints (intraStackConstraints cns)
                 , initRngPredMap = intraRangePredMap cns
                 }

instance ShowF (ArchReg arch) => Pretty (IntraJumpBounds arch ids) where
  pretty = pretty . initJumpBounds


modifyIntraStackConstraints :: (BlockIntraStackConstraints arch ids -> BlockIntraStackConstraints arch ids)
                           -> IntraJumpBounds arch ids
                           -> IntraJumpBounds arch ids
modifyIntraStackConstraints f cns = cns { intraStackConstraints = f (intraStackConstraints cns) }

------------------------------------------------------------------------
-- Execute a statement

-- | Given a statement this modifies the bounds based on the statement.
stackExecStatement :: ( MemWidth (ArchAddrWidth arch)
                      , OrdF (ArchReg arch)
                      , ShowF (ArchReg arch)
                      )
                   => BlockIntraStackConstraints arch ids
                   -> Stmt arch ids
                   -> BlockIntraStackConstraints arch ids
stackExecStatement cns stmt =
  case stmt of
    AssignStmt (Assignment aid arhs) -> do
      -- Clear all knowledge about the stack on architecture-specific
      -- functions as they may have side effects.
      --
      -- Note. This is very conservative, and we may need to improve
      -- this.
      let cns' = case arhs of
                    EvalArchFn{} -> discardStackInfo cns
                    _ -> cns
      -- Associate the given expression with a bounds.
      seq cns' $ intraStackSetAssignId aid (intraStackRhsExpr cns' aid arhs) cns'
    WriteMem addr repr val ->
      case intraStackValueExpr cns addr of
        StackOffsetExpr addrOff ->
          writeStackOff cns addrOff repr val
        -- If we write to something other than stack, then clear all
        -- stack references.
        --
        -- This is probably not a good idea in general, but seems fine
        -- for stack detection.
        _ ->
          discardStackInfo cns
    CondWriteMem{} ->
      discardStackInfo cns
    InstructionStart{} ->
      cns
    Comment{} ->
      cns
    ExecArchStmt{} ->
      discardStackInfo cns
    ArchState{} ->
      cns

-- | Update the bounds based on a statement.
execStatement :: ( MemWidth (ArchAddrWidth arch)
                 , OrdF (ArchReg arch)
                 , ShowF (ArchReg arch)
                 )
              => IntraJumpBounds arch ids
              -> Stmt arch ids
              -> IntraJumpBounds arch ids
execStatement cns stmt =
  modifyIntraStackConstraints (`stackExecStatement` stmt) cns


------------------------------------------------------------------------
-- Operations

-- | This returns the current predicate on the bound expression.
exprRangePred :: ( MemWidth (ArchAddrWidth arch)
                 , HasRepr (ArchReg arch) TypeRepr
                 , OrdF (ArchReg arch)
                 , ShowF (ArchReg arch)
                 )
              => BlockStartStackConstraints arch
              -> BlockStartRangePred arch
                 -- ^ Inferred range constraints
              -> BranchConstraints (ArchReg arch) ids
              -- ^ Bounds on assignments inferred from branch predicate.
              -> StackExpr arch ids tp
              -> MaybeRangePred tp
exprRangePred stkCns rpCns brCns e =
  case e of
    ClassRepExpr loc ->
      case MapF.lookup loc (newClassRepConstraints brCns) of
        Just (SubRange r) -> SomeRangePred r
        Nothing ->
          case locLookup loc rpCns of
            Nothing ->  NoRangePred
            Just (JustRangePred r) -> SomeRangePred r
    UninterpAssignExpr n _ -> do
      case MapF.lookup n (newUninterpAssignConstraints brCns) of
        Just (SubRange r)
          | w <- rangeWidth r
          , l <- rangeLowerBound r
          , u <- rangeUpperBound r
          , (0 < l) || (u < fromInteger (maxUnsigned w)) ->
              SomeRangePred r
        _ -> NoRangePred
    StackOffsetExpr _ -> NoRangePred
    CExpr (BVCValue w i) -> SomeRangePred (mkRangeBound w (BV.asNatural i) (BV.asNatural i))
    CExpr _ -> NoRangePred
    AppExpr n _app
      -- If a bound has been deliberately asserted to this assignment
      -- then use that.
      | Just (SubRange r) <- MapF.lookup n (newUninterpAssignConstraints brCns)
      , w <- rangeWidth r
      , l <- rangeLowerBound r
      , u <- rangeUpperBound r
      , (0 < l) || (u < fromInteger (maxUnsigned w)) ->
          SomeRangePred r
    -- Otherwise see what we can infer.
    AppExpr _n app ->
      case app of
        UExt x w
          | SomeRangePred r <- exprRangePred stkCns rpCns brCns x ->
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
          | SomeRangePred r <- exprRangePred stkCns rpCns brCns x
          , w <- rangeWidth r
          , lr <- rangeLowerBound r + fromInteger (BV.asUnsigned c)
          , ur <- rangeUpperBound r + fromInteger (BV.asUnsigned c)
          , lr `shiftR` fromIntegral (natValue w) == ur `shiftR` fromIntegral (natValue w)
          , lr' <- fromInteger (toUnsigned w (toInteger lr))
          , ur' <- fromInteger (toUnsigned w (toInteger ur)) ->
            SomeRangePred (RangePred w lr' ur')
        Trunc x w
          | SomeRangePred r <- exprRangePred stkCns rpCns brCns x
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
unsignedUpperBound cns v = do
  let stkCns = intraStackConstraints cns
  let icns = biscInitConstraints stkCns
  let valExpr = intraStackValueExpr stkCns v
  case exprRangePred icns (intraRangePredMap cns) emptyBranchConstraints valExpr of
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
data BranchConstraints r ids = BranchConstraints
  { newClassRepConstraints :: !(MapF (BoundLoc r) SubRange)
    -- ^ This maps locations to constraints on the initial values of
    -- the variable that are inferred from asserted branches.
  , newUninterpAssignConstraints :: !(MapF (AssignId ids) SubRange)
    -- ^ This maps assignments to inferred subrange constraints on
    -- assignments.
  }

instance ShowF r => Pretty (BranchConstraints r ids) where
  pretty x =
    let cl = MapF.toList (newClassRepConstraints x)
        al = MapF.toList (newUninterpAssignConstraints x)
        ppLoc :: Pair (BoundLoc r) SubRange -> Doc
        ppLoc (Pair l r) = prettyF l <+> text ":=" <+> pretty r
        ppAssign :: Pair (AssignId ids) SubRange -> Doc
        ppAssign (Pair l r) = ppAssignId l <+> text ":=" <+> pretty r
     in vcat (fmap ppLoc cl ++ fmap ppAssign al)

instance ShowF r => Show (BranchConstraints r ids) where
  show x = show (pretty x)

-- | Empty set of branch constraints.
emptyBranchConstraints :: BranchConstraints r ids
emptyBranchConstraints =
  BranchConstraints { newClassRepConstraints = MapF.empty
                    , newUninterpAssignConstraints = MapF.empty
                    }

-- | @conjoinBranchConstraints x y@ returns constraints inferred
-- from by @x@ and @y@.
conjoinBranchConstraints :: OrdF r
                         => BranchConstraints r ids
                         -> BranchConstraints r ids
                         -> BranchConstraints r ids
conjoinBranchConstraints x y =
  BranchConstraints { newClassRepConstraints =
                        MapF.union (newClassRepConstraints x) (newClassRepConstraints y)
                    , newUninterpAssignConstraints =
                        MapF.union (newUninterpAssignConstraints x) (newUninterpAssignConstraints y)
                    }

-- | @disjoinBranchConstraints x y@ returns constraints inferred that
-- @x@ or @y@ is true.
disjoinBranchConstraints :: (OrdF r, ShowF r)
                         => BranchConstraints r ids
                         -> BranchConstraints r ids
                         -> BranchConstraints r ids
disjoinBranchConstraints x y =
  BranchConstraints
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
  }

branchLocRangePred :: (u <= w)
                   => BoundLoc r (BVType w)
                   -> RangePred u
                   -> BranchConstraints r ids
branchLocRangePred l p =
  BranchConstraints { newClassRepConstraints = MapF.singleton l (SubRange p)
                    , newUninterpAssignConstraints = MapF.empty
                    }

branchAssignRangePred :: (u <= w)
                      => AssignId ids (BVType w)
                      -> RangePred u
                      -> BranchConstraints r ids
branchAssignRangePred n p =
  BranchConstraints { newClassRepConstraints = MapF.empty
                    , newUninterpAssignConstraints = MapF.singleton n (SubRange p)
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
                )
               => StackExpr arch ids (BVType w)
                 -- ^ Value we are adding bounds for.
               -> RangePred u

               -> Either String (BranchConstraints (ArchReg arch) ids)
addRangePred v rng
    -- Do nothing if upper bounds equals or exceeds maximum unsigned
    -- value.
  | bnd <- rangeUpperBound rng
  , bnd >= fromInteger (maxUnsigned (typeWidth v)) =
      Right emptyBranchConstraints
addRangePred v rng
    -- Do nothing if upper bounds equals or exceeds maximum unsigned
    -- value.
  | bnd <- rangeUpperBound rng
  , bnd >= fromInteger (maxUnsigned (typeWidth v)) =
      Right emptyBranchConstraints
addRangePred v p =
  case v of
    ClassRepExpr loc ->
      pure $ branchLocRangePred loc p
    UninterpAssignExpr aid _ ->
      pure $ branchAssignRangePred aid p
    -- Drop constraints on the offset of a stack (This should not
    -- occur in practice)
    StackOffsetExpr _i ->
      pure $! emptyBranchConstraints

    CExpr cv ->
      case cv of
        BVCValue _ c -> do
          when (BV.asUnsigned c > toInteger (rangeUpperBound p)) $ do
            Left "Constant is greater than asserted bounds."
          pure $! emptyBranchConstraints
        RelocatableCValue{} ->
          pure $! emptyBranchConstraints
        SymbolCValue{} ->
          pure $! emptyBranchConstraints

    AppExpr n a ->
      case a of
        BVAdd _ x (CExpr (BVCValue w c))
          | RangePred _wp l u <- p
          , l' <- toInteger l - BV.asUnsigned c
          , u' <- toInteger u - BV.asUnsigned c
            -- Check overflow is consistent
          , l' `shiftR` fromIntegral (natValue w) == u' `shiftR` fromIntegral (natValue w) -> do
              addRangePred x (RangePred w (fromInteger (toUnsigned w l')) (fromInteger (toUnsigned w u')))

        UExt x _outWidth
          -- If this constraint affects fewer bits than the extension,
          -- then we just propagate the property to value
          -- pre-extension.
          | Just LeqProof <- testLeq (rangeWidth p) (typeWidth x) ->
            addRangePred x p
          -- Otherwise, we still can constraint our width,
          | RangePred _ l u <- p -> do
              LeqProof <- pure (leqRefl (typeWidth x))
              addRangePred x (RangePred (typeWidth x) l u)
        -- Truncation passes through as we aonly affect low order bits.
        Trunc x _w ->
          case testLeq (rangeWidth p) (typeWidth x) of
            Just LeqProof ->
              addRangePred x p
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
           -> Either String (BranchConstraints (ArchReg arch) ids)
assertPred cns (AssignedValue a) isTrue =
  case assignRhs a of
    EvalApp (Eq x (BVValue w c)) -> do
      addRangePred (intraStackValueExpr (intraStackConstraints cns) x)
                   (mkRangeBound w (BV.asNatural c) (BV.asNatural c))
    EvalApp (Eq (BVValue w c) x) -> do
      addRangePred (intraStackValueExpr (intraStackConstraints cns) x)
                   (mkRangeBound w (BV.asNatural c) (BV.asNatural c))
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue w c)) -> do
      if isTrue then do
        when (c == BV.zero w) $ Left "x < 0 must be false."
        addRangePred (intraStackValueExpr (intraStackConstraints cns) x)  $!
          mkUpperBound (typeWidth x) (BV.asNatural c - 1)
       else do
        addRangePred (intraStackValueExpr (intraStackConstraints cns) x)  $!
          mkLowerBound (typeWidth x) (BV.asNatural c)
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue w c) y) -> do
      p <-
        if isTrue then do
          when (c == BV.maxUnsigned w) $  Left "x < max_unsigned must be true"
          pure $! mkLowerBound w (BV.asNatural c + 1)
         else do
          pure $! mkUpperBound w (BV.asNatural c)
      addRangePred (intraStackValueExpr (intraStackConstraints cns) y) p
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue w c)) -> do
      p <-
        if isTrue then
          pure $! mkUpperBound w (BV.asNatural c)
         else do
          when (c == BV.maxUnsigned w) $  Left "x < max_unsigned must be true"
          pure $! mkLowerBound w (BV.asNatural c + 1)
      addRangePred (intraStackValueExpr (intraStackConstraints cns) x) p
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue w c) y)
      | isTrue -> do
          addRangePred (intraStackValueExpr (intraStackConstraints cns) y)
                       (mkLowerBound (typeWidth y) (BV.asNatural c))
      | otherwise -> do
          when (c == BV.zero w) $ Left "0 <= x cannot be false"
          addRangePred
            (intraStackValueExpr (intraStackConstraints cns) y)
            (mkUpperBound (typeWidth y) (BV.asNatural c - 1))
    EvalApp (AndApp l r) ->
      if isTrue then
        conjoinBranchConstraints
          <$> assertPred cns l True
          <*> assertPred cns r True
      else
        disjoinBranchConstraints
          <$> assertPred cns l False
          <*> assertPred cns r False
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) ->
      if isTrue then
        -- Assert l | r
        disjoinBranchConstraints
          <$> assertPred cns l True
          <*> assertPred cns r True
      else
        -- Assert not l && not r
        conjoinBranchConstraints
          <$> assertPred cns l False
          <*> assertPred cns r False
    EvalApp (NotApp p) ->
      assertPred cns p (not isTrue)
    _ -> Right emptyBranchConstraints
assertPred _ _ _ =
  Right emptyBranchConstraints


updateRangePredMap :: ( MemWidth (ArchAddrWidth arch)
                      , HasRepr (ArchReg arch) TypeRepr
                      , OrdF (ArchReg arch)
                      , ShowF (ArchReg arch)
                      )
                   => BlockStartStackConstraints arch
                   -- ^ Constraints on stacks/registers
                   -> BranchConstraints (ArchReg arch) ids
                   -- ^ Bounds on assignments inferred from branch
                   -- predicate.
                   -> LocMap (ArchReg arch) JustRangePred
                   -> Pair (BoundLoc (ArchReg arch)) (StackExpr arch ids)
                   -> LocMap (ArchReg arch) JustRangePred
updateRangePredMap stkCns brCns m (Pair l e) = do
  case exprRangePred stkCns locMapEmpty brCns e of
    SomeRangePred r -> nonOverlapLocInsert l (JustRangePred r) m
    NoRangePred -> m

-- | Bounds for block after jump
nextBlockBounds :: forall arch ids
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids
                   -- ^ Bounds at end of this state.
                -> BranchConstraints (ArchReg arch) ids
                   -- ^ Constraints inferred from branch (or `emptyBranchConstraints)
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitJumpBounds arch
nextBlockBounds cns brCns regs = runNextStateMonad $ do
  stkCns <- postJumpStackConstraints (intraStackConstraints cns) regs
  reps <- getNextStateRepresentatives
  let icns =  biscInitConstraints (intraStackConstraints cns)
  let rngMap = foldl' (updateRangePredMap icns brCns) locMapEmpty reps
  pure $! InitJumpBounds { initBndsMap = stkCns
                         , initRngPredMap = rngMap
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

-- | Get bounds for start of block after a branch (either the true or
-- false branch)
postBranchBounds :: RegisterInfo (ArchReg arch)
                 => IntraJumpBounds arch ids -- ^ Bounds just before jump
                 -> Value arch ids BoolType -- ^ Branch condition
                 -> Bool -- ^ Flag indicating if branch predicate is true or false.
                 -> RegState (ArchReg arch) (Value arch ids)
                 -- ^ Register values at start of next state.
                 -> Either String (InitJumpBounds arch)
postBranchBounds cns c condIsTrue regs = do
  brCns <- assertPred cns c condIsTrue
  pure (nextBlockBounds cns brCns regs)


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
                     }
