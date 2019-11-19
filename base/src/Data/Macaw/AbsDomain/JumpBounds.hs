{- |

This module defines a relational abstract domain for tracking relationships
between values in registers and on stack slots.  It also maintains abstractions
of upper bounds for those values.

The overall problem being solved with this abstract domain is tracking upper
bounds on values, but under the observation that sometimes compilers generate
code that performs bounds checks on values that have been copied to the stack,
but then later uses the value from the stack rather than the register that was
checked.  Thus, we need a relational domain to track the equality between the
two values in order to learn the bounds on the copy on the stack.

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
  , functionStartBounds
  , joinInitialBounds
  , ppInitJumpBounds
  , boundsLocationInfo
  , boundsLocationRep
    -- * IntraJumpbounds
  , IntraJumpBounds
  , mkIntraJumpBounds
  , execStatement
  , postCallBounds
  , nextBlockBounds
  , postBranchBounds
  , unsignedUpperBound
  , stackOffset
    -- * Low-level details
  , ClassPred(..)
    -- ** Locations and location maps
  , BoundLoc(..)
  , LocMap
  , locMapEmpty
  , locLookup
  , locMapRegs
  , locMapStack
  , nonOverlapLocInsert
  , locOverwriteWith
    -- * Stack map
  , StackMap
  , emptyStackMap
  , stackMapReplace
  , stackMapOverwrite
  , StackMapLookup(..)
  , stackMapLookup
  , ppStackMap
  ) where

import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Bits
import           Data.Functor
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Pair
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.STRef
import           GHC.Stack
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.AbsDomain.CallParams
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import           Data.Macaw.Types hiding (Type)
import qualified Data.Macaw.Types as M

addrTypeRepr :: MemWidth w => TypeRepr (BVType w)
addrTypeRepr = BVTypeRepr memWidthNatRepr

------------------------------------------------------------------------
-- Changed

-- | A monad that can be used to record when a value is changed.
type Changed s = ReaderT (STRef s Bool) (ST s)

-- | Record the value has changed if the Boolean is true.
markChanged :: Bool -> Changed s ()
markChanged False = pure ()
markChanged True = do
  r <- ask
  lift $ writeSTRef r True

runChanged :: forall a . (forall s . Changed s a) -> Maybe a
runChanged action = runST $ do
  r <-  newSTRef False
  a <- runReaderT action r
  b <- readSTRef r
  pure $! if b then Just a else Nothing

------------------------------------------------------------------------
-- KeyPair

data KeyPair (key :: k -> Type)  (tp :: k) = KeyPair !(key tp) !(key tp)

instance TestEquality k => TestEquality (KeyPair k) where
  testEquality (KeyPair x1 x2) (KeyPair y1 y2) = do
    Refl <- testEquality x1 y1
    testEquality x2 y2

instance OrdF k => OrdF (KeyPair k) where
  compareF (KeyPair x1 x2) (KeyPair y1 y2) =
    joinOrderingF (compareF x1 y1) (compareF x2 y2)

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
  pretty (RangePred w l h) = parens (hsep [pretty (intValue w), pretty (toInteger l), pretty (toInteger h)])

------------------------------------------------------------------------
-- ClassPred

-- | This describes a constraint associated with an equivalence class
-- of registers in @InitJumpBounds@.
--
-- The first parameter is the number of bits in the
data ClassPred (w :: Nat) tp where
  -- | Predicate on bounds.
  BoundedBV :: (u <= v)
            => !(RangePred u)
            -> ClassPred w (BVType v)

  -- | Value is a offset of the stack pointer at the given offset argument.
  IsStackOffset :: {-# UNPACK #-} !(MemInt w)
              -> ClassPred w (BVType w)
  -- | No constraints on value.
  TopPred :: ClassPred w tp

ppAddend :: MemInt w -> Doc
ppAddend o | memIntValue o < 0 =
               text "-" <+> pretty (negate (toInteger (memIntValue o)))
           | otherwise = text "+" <+> pretty o

-- | Pretty print the class predicate
ppClassPred :: Doc -> ClassPred w tp -> Doc
ppClassPred d (BoundedBV p) =
  d <+> text "in" <+> pretty p
ppClassPred d (IsStackOffset i) =
  d <+> text "= stack_frame" <+> ppAddend i
ppClassPred _d TopPred =
  text ""

-- | Take the union of the old and new constraint, and record if the
-- old constraint was weakened by the new constraint.
joinClassPred :: ClassPred w tp
              -> ClassPred w tp
              -> Changed s (ClassPred w tp)
joinClassPred old new =
  case (old,new) of
    (BoundedBV ob, BoundedBV nb)
      | Just Refl <- testEquality (rangeWidth ob) (rangeWidth nb)
      , Just r <- disjoinRangePred ob nb ->
        let oldTighter = rangeLowerBound ob > rangeLowerBound ob
                      || rangeUpperBound ob < rangeUpperBound ob
         in markChanged oldTighter $> BoundedBV r
    (IsStackOffset i, IsStackOffset j)
      | i == j -> pure $! old
    (TopPred,_) -> pure TopPred
    (_,_) -> markChanged True $> TopPred

------------------------------------------------------------------------
-- BoundLoc

-- | Either a register or stack offset.
--
-- These locations are tracked by our bounds analysis algorithm.
data BoundLoc (r :: M.Type -> Type) (tp :: M.Type) where
  -- | @RegLoc r@ denotes the register @r@.
  RegLoc :: !(r tp) -> BoundLoc r tp
  -- | @StackkOffLoc o repr@ denotes the bytes from address range
  -- @[initSP + o .. initSP + o + memReprBytes repr)@.
  --
  -- We should note that this makes no claim that those addresses
  -- are valid.
  StackOffLoc :: !(MemInt (RegAddrWidth r))
              -> !(MemRepr tp)
              -> BoundLoc r tp

instance TestEquality r => TestEquality (BoundLoc r) where
  testEquality (RegLoc x) (RegLoc y) = testEquality x y
  testEquality (StackOffLoc xi xr) (StackOffLoc yi yr) | xi == yi =
    testEquality xr yr
  testEquality _ _ = Nothing

instance HasRepr r TypeRepr => HasRepr (BoundLoc r) TypeRepr where
  typeRepr (RegLoc r) = typeRepr r
  typeRepr (StackOffLoc _ r) = typeRepr r

instance OrdF r => OrdF (BoundLoc r) where
  compareF (RegLoc x) (RegLoc y) = compareF x y
  compareF (RegLoc _) _ = LTF
  compareF _ (RegLoc _) = GTF

  compareF (StackOffLoc xi xr) (StackOffLoc yi yr) =
    case compare xi yi of
      LT -> LTF
      GT -> GTF
      EQ -> compareF xr yr

instance ShowF r => Pretty (BoundLoc r tp) where
  pretty (RegLoc r) = text (showF r)
  pretty (StackOffLoc i tp) =
    text "*(stack_frame " <+> ppAddend i <> text ") :" <> pretty tp

instance ShowF r => PrettyF (BoundLoc r) where
  prettyF = pretty

------------------------------------------------------------------------
-- LocConstraint

-- | A constraint on a @BoundLoc
data LocConstraint r tp where
  -- | An equivalence class representative with the given number of
  -- elements.
  --
  -- In our map the number of equivalence class members should always
  -- be positive.
  ValueRep :: !(ClassPred (RegAddrWidth r) tp)
           -> LocConstraint r tp
  EqualValue :: !(BoundLoc r tp)
             -> LocConstraint r tp

unconstrained :: LocConstraint r tp
unconstrained = ValueRep TopPred

ppLocConstraint :: ShowF r => Doc -> LocConstraint r tp -> Doc
ppLocConstraint d (ValueRep p) = ppClassPred d p
ppLocConstraint d (EqualValue v) = d <+> text "=" <+> pretty v

------------------------------------------------------------------------
-- MemVal

-- | A value with a particular type along with a MemRepr indicating
-- how the type is encoded in memory.
data MemVal (p :: M.Type -> Type) =
  forall (tp :: M.Type) . MemVal !(MemRepr tp) !(p tp)

instance FunctorF MemVal where
  fmapF f (MemVal r x) = MemVal r (f x)

ppStackOff :: MemInt w -> MemRepr tp -> Doc
ppStackOff o repr =
  text "*(stack_frame" <+> ppAddend o <> text "," <+> pretty repr <> text ")"

------------------------------------------------------------------------
-- StackMap

-- | This is a data structure for representing values written to
-- concrete stack offsets.
newtype StackMap w (v :: M.Type -> Type) = SM (Map (MemInt w) (MemVal v))

instance FunctorF (StackMap w) where
  fmapF f (SM m) = SM (fmap (fmapF f) m)

-- | Empty stack map
emptyStackMap :: StackMap w p
emptyStackMap = SM Map.empty

-- | Pretty print a stack map given a term
ppStackMap :: (forall tp . Doc -> v tp -> Doc) -> StackMap w v -> Doc
ppStackMap f (SM m)
  | Map.null m = text "empty-stack-map"
  | otherwise =
      vcat $
      [ f (ppStackOff o repr) v
      | (o,MemVal repr v) <- Map.toList m
      ]

instance PrettyF v => Pretty (StackMap w v) where
  pretty = ppStackMap (\nm d -> nm <+> text ":=" <+> prettyF d)

-- | Result returned by @stackMapLookup@.
data StackMapLookup w p tp where
  -- 1| We found a value at the exact offset and repr
  SMLResult :: !(p tp) -> StackMapLookup w p tp
  -- | We found a value that had an overlapping offset and repr.
  SMLOverlap  :: !(MemInt w)
              -> !(MemRepr utp)
              -> !(p utp)
              -> StackMapLookup w p tp
  -- | We found neither an exact match nor an overlapping write.
  SMLNone :: StackMapLookup w p tp

-- | Lookup value (if any) at given offset and representation.
stackMapLookup :: MemWidth w
               => MemInt w
               -> MemRepr tp
               -> StackMap w p
               -> StackMapLookup w p tp
stackMapLookup off repr (SM m) =  do
  let end = off + fromIntegral (memReprBytes repr)
  if end < off then
    error $ "stackMapLookup given bad offset."
   else
    case Map.lookupLT end m of
      Just (oldOff, MemVal oldRepr val)
          -- If match exact
        | oldOff == off
        , Just Refl <- testEquality oldRepr repr ->
          SMLResult val
        -- If previous write ends after this write  starts
        | oldOff + fromIntegral (memReprBytes oldRepr) > off ->
          SMLOverlap oldOff oldRepr val
        | otherwise ->
          SMLNone
      Nothing -> SMLNone

clearPreWrites :: Ord i => i -> i -> Map i v -> Map i v
clearPreWrites l h m =
  case Map.lookupLT h m of
    Just (o,_v) | o >= l -> clearPreWrites l h (Map.delete o m)
    _ -> m

clearPostWrites :: Ord i => i -> i -> Map i v -> Map i v
clearPostWrites l h m =
  case Map.lookupGE l m of
    Just (o,_v) | o < h -> clearPostWrites l h (Map.delete o m)
    _ -> m

-- | This updates the stack map with a write if this write is either
-- unreserved or completely replaces an existing write.
stackMapReplace :: forall w p tp
                .  (MemWidth w, HasCallStack)
                => MemInt w
                -> MemRepr tp
                -> p tp
                -> StackMap w p
                -> Either (MemInt w, Pair MemRepr p) (StackMap w p)
stackMapReplace off repr val (SM m) = do
  let end = off + fromIntegral (memReprBytes repr)
  -- If overflow occured in address then raise error.
  when (end < off) $ error "Invalid stack offset"

  case Map.lookupLE end m of
    Nothing -> pure ()
    Just (oldOff, MemVal oldRepr oldVal)
      -- Previous write ends before this write.
      | oldOff + fromIntegral (memReprBytes oldRepr) <= off ->
          pure ()
      -- This write replaces a previous write
      | oldOff == off, memReprBytes oldRepr == memReprBytes repr ->
          pure ()
      -- This write overlaps without completely replacing
      | otherwise ->
          Left (oldOff, Pair oldRepr oldVal)
  -- Update map
  pure $! SM (Map.insert off (MemVal repr val) m)

-- | This assigns a region of bytes to a particular value in the stack.
--
-- It overwrites any values that overlap with the location.
stackMapOverwrite :: forall w p tp
                  .  MemWidth w
                  => MemInt w -- ^ Offset in the stack to write to
                  -> MemRepr tp -- ^ Type of value to write
                  -> p tp  -- ^ Value to write
                  -> StackMap w p
                  -> StackMap w p
stackMapOverwrite off repr v (SM m) =
  let e = off + fromIntegral (memReprBytes repr)
   in SM $ Map.insert off (MemVal repr v)
         $ clearPreWrites off e
         $ clearPostWrites off e m

-- | This sets the value at an offset without checking to clear any
-- previous writes to values.
unsafeStackMapInsert :: MemInt w -> MemRepr tp -> p tp -> StackMap w p -> StackMap w p
unsafeStackMapInsert o repr v (SM m) = SM (Map.insert o (MemVal repr v) m)

stackMapFoldrWithKey :: (forall tp . MemInt w -> MemRepr tp -> v tp -> r -> r)
                     -> r
                     -> StackMap w v
                     -> r
stackMapFoldrWithKey f z (SM m) =
  Map.foldrWithKey (\k (MemVal repr v) r -> f k repr v r) z m

stackMapTraverseWithKey_ :: Applicative m
                         => (forall tp . MemInt w -> MemRepr tp -> v tp -> m ())
                         -> StackMap w v
                         -> m ()
stackMapTraverseWithKey_ f (SM m) =
  Map.foldrWithKey (\k (MemVal repr v) r -> f k repr v *> r) (pure ()) m

stackMapMapWithKey :: (forall tp . MemInt w -> MemRepr tp -> a tp -> b tp)
                   -> StackMap w a
                   -> StackMap w b
stackMapMapWithKey f (SM m) =
  SM (Map.mapWithKey (\o (MemVal repr v) -> MemVal repr (f o repr v)) m)

stackMapTraverseMaybeWithKey :: Applicative m
                             => (forall tp . MemInt w -> MemRepr tp -> a tp -> m (Maybe (b tp)))
                                -- ^ Traversal function
                             -> StackMap w a
                             -> m (StackMap w b)
stackMapTraverseMaybeWithKey f (SM m) =
  SM <$> Map.traverseMaybeWithKey (\o (MemVal repr v) -> fmap (MemVal repr) <$> f o repr v) m

-- @stackMapDropAbove bnd m@ includes only entries in @m@ whose bytes do not go above @bnd@.
stackMapDropAbove :: MemWidth w => Integer -> StackMap w p -> StackMap w p
stackMapDropAbove bnd (SM m) = SM (Map.filterWithKey p m)
  where p o (MemVal r _) = toInteger o  + toInteger (memReprBytes r) <= bnd

-- @stackMapDropBelow bnd m@ includes only entries in @m@ whose bytes do not go below @bnd@.
stackMapDropBelow :: MemWidth w => Integer -> StackMap w p -> StackMap w p
stackMapDropBelow bnd (SM m) = SM (Map.filterWithKey p m)
  where p o _ = toInteger o >= bnd

------------------------------------------------------------------------
-- LocMap

-- | A map from register/concrete stack offsets to values
data LocMap (r :: M.Type -> Type) (v :: M.Type -> Type)
  = LocMap { locMapRegs :: !(MapF r v)
           , locMapStack :: !(StackMap (RegAddrWidth r) v)
           }

-- | An empty location map.
locMapEmpty :: LocMap r v
locMapEmpty = LocMap { locMapRegs = MapF.empty, locMapStack = emptyStackMap }

-- | Return value associated with location or nothing if it is not
-- defined.
locLookup :: (MemWidth (RegAddrWidth r), OrdF r)
          => BoundLoc r tp
          -> LocMap r v
          -> Maybe (v tp)
locLookup (RegLoc r) m = MapF.lookup r (locMapRegs m)
locLookup (StackOffLoc o repr) m =
  case stackMapLookup o repr (locMapStack m) of
    SMLResult r -> Just r
    SMLOverlap _ _ _ -> Nothing
    SMLNone -> Nothing

-- | This associates the location with a value in the map, replacing any existing binding.
--
-- It is prefixed with "nonOverlap" because it doesn't guarantee that stack
-- values are non-overlapping -- the user should ensure this before calling this.
nonOverlapLocInsert :: OrdF r => BoundLoc r tp -> v tp -> LocMap r v -> LocMap r v
nonOverlapLocInsert (RegLoc r) v m =
  m { locMapRegs = MapF.insert r v (locMapRegs m) }
nonOverlapLocInsert (StackOffLoc off repr) v m =
  m { locMapStack = unsafeStackMapInsert off repr v (locMapStack m) }

locOverwriteWith :: (OrdF r, MemWidth (RegAddrWidth r))
                 => (v tp -> v tp -> v tp) -- ^ Update takes new and  old.
                 -> BoundLoc r tp
                 -> v tp
                 -> LocMap r v
                 -> LocMap r v
locOverwriteWith upd (RegLoc r) v m =
  m { locMapRegs = MapF.insertWith upd r v (locMapRegs m) }
locOverwriteWith upd (StackOffLoc o repr) v m =
  let nv = case stackMapLookup o repr (locMapStack m) of
             SMLNone -> v
             SMLOverlap _ _ _ -> v
             SMLResult oldv -> upd v oldv
   in m { locMapStack = stackMapOverwrite o repr nv (locMapStack m) }

------------------------------------------------------------------------
-- InitJumpBounds

-- | Bounds for a function as the start of a block.
newtype InitJumpBounds arch
   = InitJumpBounds { initBndsMap :: LocMap (ArchReg arch) (LocConstraint (ArchReg arch))
                    }

-- | Pretty print jump bounds.
ppInitJumpBounds :: forall arch
                    . ShowF (ArchReg arch) => InitJumpBounds arch -> [Doc]
ppInitJumpBounds (InitJumpBounds m)
  = flip (MapF.foldrWithKey (\k v -> (ppLocConstraint (text (showF k)) v:)))
                            (locMapRegs m)
  $ stackMapFoldrWithKey (\i repr v -> (ppLocConstraint (ppStackOff i repr) v:))
                         []
                         (locMapStack m)

instance ShowF (ArchReg arch) => Pretty (InitJumpBounds arch) where
  pretty = vcat . ppInitJumpBounds

instance ShowF (ArchReg arch) => Show (InitJumpBounds arch) where
  show = show . pretty

-- | Bounds at start of function.
functionStartBounds :: RegisterInfo (ArchReg arch) => InitJumpBounds arch
functionStartBounds =
  let m = LocMap { locMapRegs = MapF.singleton sp_reg (ValueRep (IsStackOffset 0))
                 , locMapStack = emptyStackMap
                 }
   in InitJumpBounds m

-- | Return the representative and  predicate associated with the location in the map.
locConstraint :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
              => InitJumpBounds arch
              -> BoundLoc (ArchReg arch) tp
              -> LocConstraint (ArchReg arch) tp
locConstraint (InitJumpBounds m) l = fromMaybe unconstrained (locLookup l m)

-- | @boundsLocationInfo bnds loc@ returns a triple containing the
-- class representative, predicate, and class size associated the
-- location.
boundsLocationInfo :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                   => InitJumpBounds arch
                   -> BoundLoc (ArchReg arch) tp
                   -> ( BoundLoc (ArchReg arch) tp
                      , ClassPred (ArchAddrWidth arch) tp
                      )
boundsLocationInfo bnds l =
  case locConstraint bnds l of
    EqualValue loc -> boundsLocationInfo bnds loc
    ValueRep p -> (l, p)

-- | @boundsLocRep bnds loc@ returns the representative location for
-- @loc@.
--
-- This representative location has the property that a location must
-- have the same value as its representative location, and if two
-- locations have provably equal values in the bounds, then they must
-- have the same representative.
boundsLocationRep :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> BoundLoc (ArchReg arch) tp
                  -> BoundLoc (ArchReg arch) tp
boundsLocationRep bnds l =
  case boundsLocationInfo bnds l of
    (r,_) -> r

-- | The the location to have the given constraint in the bounds, and
-- return the new bounds.
setLocConstraint :: OrdF (ArchReg arch)
                 => BoundLoc (ArchReg arch) tp
                 -> LocConstraint (ArchReg arch) tp
                 -> InitJumpBounds arch
                 -> InitJumpBounds arch
setLocConstraint l c (InitJumpBounds m) =
  InitJumpBounds (nonOverlapLocInsert l c m)

-- | Join locations
joinNewLoc :: forall s arch tp
           .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
           => InitJumpBounds arch
           -> InitJumpBounds arch
           -> STRef s (InitJumpBounds arch)
           -- ^ The current index bounds.
           -> STRef s (MapF (KeyPair (BoundLoc (ArchReg arch))) (BoundLoc (ArchReg arch)))
           -- ^ The map from (oldClassRep, newClassRep) pairs to the
           -- result class rep.
           -> STRef s Int
           -- ^ Stores the number of equivalence classes we have seen in
           -- in the old class
           -- Used so determining if any classes are changed.
           -> BoundLoc (ArchReg arch) tp
              -- ^ Location in join that we have not yet visited.
           -> LocConstraint (ArchReg arch) tp
              -- ^ Constraint on location in original list.
           -> Changed s ()
joinNewLoc old new bndsRef procRef cntr thisLoc oldCns = do
  (oldRep, oldPred) <- lift $
    case oldCns of
      ValueRep p -> do
        -- Increment number of equivalence classes when we see an old
        -- representative.
        modifySTRef' cntr (+1)
        -- Return this loc
        pure (thisLoc, p)
      EqualValue  oldLoc ->
        pure (boundsLocationInfo old oldLoc)
  let (newRep, newPred) = boundsLocationInfo new thisLoc
  m <- lift $ readSTRef procRef
  -- See if we have already added a representative for this class.
  let pair = KeyPair oldRep newRep
  case MapF.lookup pair m of
    Nothing -> do
      p <- joinClassPred oldPred newPred
      lift $ do
        writeSTRef procRef $! MapF.insert pair thisLoc m
        case p of
          TopPred -> pure ()
          _ -> modifySTRef' bndsRef $ setLocConstraint thisLoc (ValueRep p)
    Just resRep ->
      -- Assert r is equal to resRep
      lift $ modifySTRef' bndsRef $
        setLocConstraint thisLoc (EqualValue resRep)

-- | Bounds where there are no constraints.
emptyInitialBounds :: InitJumpBounds arch
emptyInitialBounds = InitJumpBounds locMapEmpty

-- | Return a jump bounds that implies both input bounds, or `Nothing`
-- if every fact inx the old bounds is implied by the new bounds.
joinInitialBounds :: forall arch
                  .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> InitJumpBounds arch
                  -> Maybe (InitJumpBounds arch)
joinInitialBounds old new = runChanged $ do
  -- Reference to new bounds.
  bndsRef <- lift $ newSTRef emptyInitialBounds
  -- This maps pairs containing the class representative in the old
  -- and new maps to the associated class representative in the
  -- combined bounds.
  procRef <- lift $ newSTRef MapF.empty
  cntr    <- lift $ newSTRef 0
  --
  MapF.traverseWithKey_
    (\r -> joinNewLoc old new bndsRef procRef cntr (RegLoc r))
    (locMapRegs (initBndsMap old))
  stackMapTraverseWithKey_
    (\i r c -> joinNewLoc old new bndsRef procRef cntr (StackOffLoc i r) c)
    (locMapStack (initBndsMap old))

  -- Check number of equivalence classes in result and original
  -- The count should not have decreased, but may increase if two elements
  -- are no longer equal, and we need to check this.
  origClassCount <- lift $ readSTRef cntr
  resultClassCount <- lift $ MapF.size <$> readSTRef procRef
  unless (origClassCount <= resultClassCount) $ do
    error "Original class count should be bound by resultClassCount"
  -- Record changed if any classes are different.
  markChanged (origClassCount < resultClassCount)

  lift $ readSTRef bndsRef

------------------------------------------------------------------------
-- BoundExpr

-- | This is an expression that represents the value of stack
-- locations and assignments during steping through the block.
--
-- The main diference between this and
-- the `Value` type, index expressions do not depend on values read
-- and written to memory during execution of the block, and are purely
-- functions of the input
--
-- This is different from `ClassPred` in that @ClassPred@ is a property
-- assigned to equivalence classes
data BoundExpr arch ids tp where
  -- | This refers to the contents of the location at the start
  -- of block execution.
  --
  -- The location should be a class representative in the initial bounds.
  ClassRepExpr :: !(BoundLoc (ArchReg arch) tp) -> BoundExpr arch ids tp
  -- | An assignment that is not interpreted, and just treated as a constant.
  UninterpAssignExpr :: !(AssignId ids tp)
                     -> !(TypeRepr tp)
                     -> BoundExpr arch ids tp
  -- | Denotes the value of the stack pointer at function start plus some constant.
  StackOffsetExpr :: !(MemInt (ArchAddrWidth arch))
                  -> BoundExpr arch ids (BVType (ArchAddrWidth arch))
  -- | Denotes a constant
  CExpr :: !(CValue arch tp) -> BoundExpr arch ids tp

  -- | This is a pure function applied to other index expressions that
  -- may be worth interpreting (but could be treated as an uninterp
  -- assign expr also.
  AppExpr :: !(AssignId ids tp)
          -> !(App (BoundExpr arch ids) tp)
          -> BoundExpr arch ids tp

instance TestEquality (ArchReg arch) => TestEquality (BoundExpr arch ids) where
  testEquality (ClassRepExpr x) (ClassRepExpr y) =
    testEquality x y
  testEquality (UninterpAssignExpr x _) (UninterpAssignExpr y _) =
    testEquality x y
  testEquality (StackOffsetExpr x) (StackOffsetExpr y) =
    if x == y then
      Just Refl
     else
      Nothing
  testEquality (CExpr x) (CExpr y) =
    testEquality x y
  testEquality (AppExpr xn _xa) (AppExpr yn _ya) =
    testEquality xn yn
  testEquality _ _ = Nothing

instance OrdF (ArchReg arch) => OrdF (BoundExpr arch ids) where
  compareF (ClassRepExpr x) (ClassRepExpr y) = compareF x y
  compareF ClassRepExpr{} _ = LTF
  compareF _ ClassRepExpr{} = GTF

  compareF (UninterpAssignExpr x _) (UninterpAssignExpr y _) = compareF x y
  compareF UninterpAssignExpr{} _ = LTF
  compareF _ UninterpAssignExpr{} = GTF

  compareF (StackOffsetExpr x) (StackOffsetExpr y) = fromOrdering (compare x y)
  compareF StackOffsetExpr{} _ = LTF
  compareF _ StackOffsetExpr{} = GTF

  compareF (CExpr x) (CExpr y) = compareF x y
  compareF CExpr{} _ = LTF
  compareF _ CExpr{} = GTF

  compareF (AppExpr xn _xa) (AppExpr yn _ya) = compareF xn yn

instance ( HasRepr (ArchReg arch) TypeRepr
         , MemWidth (ArchAddrWidth arch)
         ) => HasRepr (BoundExpr arch ids) TypeRepr where
  typeRepr e =
    case e of
      ClassRepExpr x    -> typeRepr x
      UninterpAssignExpr _ tp   -> tp
      StackOffsetExpr _ -> addrTypeRepr
      CExpr x           -> typeRepr x
      AppExpr _ a       -> typeRepr a

instance ShowF (ArchReg arch) => Pretty (BoundExpr arch id tp) where
  pretty e =
    case e of
      ClassRepExpr l -> pretty l
      UninterpAssignExpr n _ -> parens (text "uninterp" <+> ppAssignId n)
      StackOffsetExpr o -> parens (text "+ stack_off" <+> pretty o)
      CExpr v -> pretty v
      AppExpr n _ -> parens (text "app" <+> ppAssignId n)

instance ShowF (ArchReg arch) => PrettyF (BoundExpr arch id) where
  prettyF = pretty

------------------------------------------------------------------------
-- IntraJumpBounds

-- | Information about bounds for a particular value within a block.
data IntraJumpBounds arch ids
   = IntraJumpBounds { initBounds :: !(LocMap (ArchReg arch) (LocConstraint (ArchReg arch)))
                       -- ^ Bounds at execution start.
                       --
                       -- This may have been refined by branch predicates.
                     , stackExprMap :: !(StackMap (ArchAddrWidth arch) (BoundExpr arch ids))
                        -- ^ Maps stack offsets to the expression associated with them.
                     , assignExprMap :: !(MapF (AssignId ids) (BoundExpr arch ids))
                       -- ^ Maps processed assignments to index expressions.
                     , memoTable :: !(MapF (App (BoundExpr arch ids)) (BoundExpr arch ids))
                       -- ^ Table for ensuring each bound expression
                       -- has a single representative.
                     }

-- | Return an expression equivalent to the location in the constraint
-- map.
--
-- This attempts to normalize the expression to get a representative.
locExpr :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
        => LocMap (ArchReg arch) (LocConstraint (ArchReg arch))
        -> BoundLoc (ArchReg arch) tp
        -> BoundExpr arch ids tp
locExpr m loc =
  case locLookup loc m of
    Nothing -> ClassRepExpr loc
    Just (EqualValue loc') -> locExpr m loc'
    Just (ValueRep p) ->
      case p of
        IsStackOffset i -> StackOffsetExpr i
        BoundedBV _ -> ClassRepExpr loc
        TopPred -> ClassRepExpr loc

-- | Create index bounds from initial index bounds.
mkIntraJumpBounds :: forall arch ids
                  .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> IntraJumpBounds arch ids
mkIntraJumpBounds (InitJumpBounds initBnds) = do
  let -- Map stack offset and memory annotation pair to the
      -- representative in the initial bounds.
      stackExpr :: MemInt (ArchAddrWidth arch)
                -> MemRepr tp
                -> LocConstraint (ArchReg arch) tp
                -> BoundExpr arch ids tp
      stackExpr i tp _ = locExpr initBnds (StackOffLoc i tp)
   in IntraJumpBounds { initBounds     = initBnds
                      , stackExprMap   = stackMapMapWithKey stackExpr (locMapStack initBnds)
                      , assignExprMap  = MapF.empty
                      , memoTable      = MapF.empty
                      }

-- | Return the value of the index expression given the bounds.
valueExpr :: forall arch ids tp
          .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
          => IntraJumpBounds arch ids
          -> Value arch ids tp
          -> BoundExpr arch ids tp
valueExpr bnds val =
  case val of
    CValue c -> CExpr c
    AssignedValue (Assignment aid _) ->
      case MapF.lookup aid (assignExprMap bnds) of
        Just e -> e
        Nothing -> error $ "valueExpr internal: Expected value to be assigned."
    Initial r -> locExpr (initBounds bnds) (RegLoc r)

-- | Return stack offset if value is a stack offset.
stackOffset :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
            => IntraJumpBounds arch ids
            -> Value arch ids (BVType (ArchAddrWidth arch))
            -> Maybe (MemInt (ArchAddrWidth arch))
stackOffset bnds val =
  case valueExpr bnds val of
    StackOffsetExpr i -> Just i
    _ -> Nothing

-- | Update the stack to point to the given expression.
writeStackOff :: forall arch ids tp
              .  (MemWidth (ArchAddrWidth arch), OrdF  (ArchReg arch))
              => IntraJumpBounds arch ids
              -> MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> Value arch ids tp
              -> IntraJumpBounds arch ids
writeStackOff bnds off repr v =
  bnds { stackExprMap = stackMapOverwrite off repr (valueExpr bnds v) (stackExprMap bnds) }

-- | Return an index expression associated with the @AssignRhs@.
rhsExpr :: forall arch ids tp
        .  ( MemWidth (ArchAddrWidth arch)
           , OrdF (ArchReg arch)
           , ShowF (ArchReg arch)
           )
        => IntraJumpBounds arch ids
        -> AssignId ids tp
        -> AssignRhs arch (Value arch ids) tp
        -> BoundExpr arch ids tp
rhsExpr bnds aid arhs =
  case arhs of
    EvalApp app -> do
      let stackFn v = toInteger <$> stackOffset bnds v
      case appAsStackOffset stackFn app of
        Just (StackOffsetView o) -> do
          StackOffsetExpr $ fromInteger o
        _ -> do
          let a = fmapFC (valueExpr bnds) app
          case MapF.lookup a (memoTable bnds) of
            Just r -> r
            Nothing -> AppExpr aid a
    ReadMem addr repr
      | Just o <- stackOffset bnds addr
      , SMLResult e <- stackMapLookup o repr (stackExprMap bnds) ->
        e
    _ -> UninterpAssignExpr aid (typeRepr arhs)

-- | Associate the given bound expression with the assignment.
bindAssignment :: IntraJumpBounds arch ids
               -> AssignId ids tp
               -> BoundExpr arch ids tp
               -> IntraJumpBounds arch ids
bindAssignment bnds aid expr =
  bnds { assignExprMap = MapF.insert aid expr (assignExprMap bnds) }

-- | Discard information about the stack in the bounds due to an
-- operation that may affect the stack.
discardStackInfo :: IntraJumpBounds arch ids
                 -> IntraJumpBounds arch ids
discardStackInfo bnds = bnds { stackExprMap = emptyStackMap }

-- | Given a statement this modifies the bounds based on the statement.
execStatement :: ( MemWidth (ArchAddrWidth arch)
                 , OrdF (ArchReg arch)
                 , ShowF (ArchReg arch)
                 )
              => IntraJumpBounds arch ids
              -> Stmt arch ids
              -> IntraJumpBounds arch ids
execStatement bnds stmt =
  case stmt of
    AssignStmt (Assignment aid arhs) -> do
      -- Clear all knowledge about the stack on architecture-specific
      -- functions as they may have side effects.
      --
      -- Note. This is very conservative, and we may need to improve
      -- this.
      let bnds' = case arhs of
                    EvalArchFn{} -> discardStackInfo bnds
                    _ -> bnds
      -- Associate the given expression with a bounds.
      seq bnds' $ bindAssignment bnds' aid (rhsExpr bnds' aid arhs)
    WriteMem addr repr val ->
      case stackOffset bnds addr of
        Just addrOff ->
          writeStackOff bnds addrOff repr val
        -- If we write to something other than stack, then clear all stack references.
        Nothing ->
          discardStackInfo bnds
    CondWriteMem{} ->
      discardStackInfo bnds
    InstructionStart{} ->
      bnds
    Comment{} ->
      bnds
    ExecArchStmt{} ->
      discardStackInfo bnds
    ArchState{} ->
      bnds

instance ShowF (ArchReg arch) => Pretty (IntraJumpBounds arch ids) where
  pretty bnds = pretty (InitJumpBounds (initBounds bnds))

------------------------------------------------------------------------
-- Operations

-- | Return predicate from constant.
cvaluePred :: CValue arch tp -> ClassPred (ArchAddrWidth arch) tp
cvaluePred v =
  case v of
    BoolCValue _ -> TopPred
    BVCValue w i -> BoundedBV (mkRangeBound w (fromInteger i) (fromInteger i))
    RelocatableCValue{} -> TopPred
    SymbolCValue{} -> TopPred

-- | This returns the current predicate on the bound expression.
exprPred :: ( MemWidth (ArchAddrWidth arch)
            , HasRepr (ArchReg arch) TypeRepr
            , OrdF (ArchReg arch)
            , ShowF (ArchReg arch)
            )
         => LocMap (ArchReg arch) (LocConstraint (ArchReg arch))
            -- ^ Constraints on stacks/registers
         -> BranchConstraints (ArchReg arch) ids
            -- ^ Bounds on assignments inferred from branch predicate.
         -> BoundExpr arch ids tp
         -> ClassPred (ArchAddrWidth arch) tp
exprPred lm brCns v =
  case v of
    ClassRepExpr loc ->
      case MapF.lookup loc (newClassRepConstraints brCns) of
        Just (SubRange r) -> BoundedBV r
        Nothing ->
          case boundsLocationInfo (InitJumpBounds lm) loc of
            (_,p) -> p
    UninterpAssignExpr n _ -> do
      case MapF.lookup n (newUninterpAssignConstraints brCns) of
        Just (SubRange r)
          | w <- rangeWidth r
          , l <- rangeLowerBound r
          , u <- rangeUpperBound r
          , (0 < l) || (u < fromInteger (maxUnsigned w)) ->
              BoundedBV r
        _ -> TopPred
    StackOffsetExpr x -> IsStackOffset x
    CExpr c -> cvaluePred c
    AppExpr n _app
      -- If a bound has been deliberately asserted to this assignment
      -- then use that.
      | Just (SubRange r) <- MapF.lookup n (newUninterpAssignConstraints brCns)
      , w <- rangeWidth r
      , l <- rangeLowerBound r
      , u <- rangeUpperBound r
      , (0 < l) || (u < fromInteger (maxUnsigned w)) ->
          BoundedBV r
    -- Otherwise see what we can infer.
    AppExpr _n app ->
      case app of
        UExt x w
          | BoundedBV r <- exprPred lm brCns x ->
              -- If bound covers all the bits in x, then we can extend it to all
              -- the bits in result (since new bits are false)
              --
              -- Otherwise, we only have the partial bound
              case testEquality (rangeWidth r) (typeWidth x) of
                Just Refl ->
                  BoundedBV (mkRangeBound w (rangeLowerBound r) (rangeUpperBound r))
                Nothing ->
                  -- Dynamic check on range width that should never fail.
                  case testLeq (rangeWidth r) w of
                    Just LeqProof -> BoundedBV r
                    Nothing -> error "exprPred given malformed app."
        BVAdd _ x (CExpr (BVCValue _ c))
          | BoundedBV r <- exprPred lm brCns x
          , w <- rangeWidth r
          , lr <- rangeLowerBound r + fromInteger (toUnsigned w c)
          , ur <- rangeUpperBound r + fromInteger (toUnsigned w c)
          , lr `shiftR` fromIntegral (natValue w) == ur `shiftR` fromIntegral (natValue w)
          , lr' <- fromInteger (toUnsigned w (toInteger lr))
          , ur' <- fromInteger (toUnsigned w (toInteger ur)) ->
            BoundedBV (RangePred w lr' ur')
        Trunc x w
          | BoundedBV r <- exprPred lm brCns x
            -- Compare the range constraint with the output number of bits.
            -- If the bound on r covers at most the truncated number
            -- of bits, then we just pass it through.
          , Just LeqProof <- testLeq (rangeWidth r) w ->
            BoundedBV r
{-
        BVAnd _ x y ->
          case (exprPred lm brCns x,  exprPred lm brCns y) of
            (BoundedBV (UBVUpperBound xw xb), BoundedBV (UBVUpperBound yw yb))
              | Just Refl <- testEquality xw yw ->
                  BoundedBV (UBVUpperBound xw (min xb yb))
            (TopPred, yb) -> yb
            (xb, _)       -> xb
        SExt x w ->
          case exprPred lm brCns x of
            BoundedBV (UBVUpperBound u b) ->
              case testLeq u w of
                Just LeqProof -> BoundedBV (UBVUpperBound u b)
                Nothing -> error "unsignedUpperBound given bad width"
            _ -> TopPred
-}
        _ -> TopPred

-- | This attempts to resolve the predicate associated with a value.
--
-- This does not make use of any branch constraints.
valuePred :: ( MapF.OrdF (ArchReg arch)
             , MapF.ShowF (ArchReg arch)
             , RegisterInfo (ArchReg arch)
             )
          => IntraJumpBounds arch ids
          -> Value arch ids tp
          -> ClassPred (ArchAddrWidth arch) tp
valuePred bnds v =
  case v of
    CValue cv -> cvaluePred cv
    AssignedValue a ->
      case MapF.lookup (assignId a) (assignExprMap bnds) of
        Just valExpr ->
          exprPred (initBounds bnds) emptyBranchConstraints valExpr
        Nothing -> TopPred
    Initial r ->
      case boundsLocationInfo (InitJumpBounds (initBounds bnds)) (RegLoc r) of
        (_,p) -> p

-- | This returns a natural number with a computed upper bound for the
-- value or `Nothing` if no explicit bound was inferred.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => IntraJumpBounds arch ids
                   -> Value arch ids tp
                   -> Maybe Natural
unsignedUpperBound bnds v =
  case valuePred bnds v of
    BoundedBV r -> do
      Refl <- testEquality (rangeWidth r) (typeWidth v)
      pure (rangeUpperBound r)
    _ -> Nothing

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
               => BoundExpr arch ids (BVType w)
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
          when (toUnsigned (rangeWidth p) c > toInteger (rangeUpperBound p)) $ do
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
          , l' <- toInteger l - c
          , u' <- toInteger u - c
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
assertPred bnds (AssignedValue a) isTrue =
  case assignRhs a of
    EvalApp (Eq x (BVValue w c)) -> do
      addRangePred (valueExpr bnds x) (mkRangeBound w (fromInteger c) (fromInteger c))
    EvalApp (Eq (BVValue w c) x) -> do
      addRangePred (valueExpr bnds x) (mkRangeBound w (fromInteger c) (fromInteger c))
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c)) -> do
      if isTrue then do
        when (c == 0) $ Left "x < 0 must be false."
        addRangePred (valueExpr bnds x)  $! mkUpperBound (typeWidth x) (fromInteger (c-1))
       else do
        addRangePred (valueExpr bnds x)  $! mkLowerBound (typeWidth x) (fromInteger c)
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue w c) y) -> do
      p <-
        if isTrue then do
          when (c >= maxUnsigned w) $  Left "x <= max_unsigned must be true"
          pure $! mkLowerBound w (fromInteger (c+1))
         else do
          pure $! mkUpperBound w (fromInteger c)
      addRangePred (valueExpr bnds y) p
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue w c)) -> do
      p <-
        if isTrue then
          pure $! mkUpperBound w (fromInteger c)
         else do
          when (c >= maxUnsigned w) $  Left "x <= max_unsigned must be true"
          pure $! mkLowerBound w (fromInteger (c+1))
      addRangePred (valueExpr bnds x) p
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y)
      | isTrue -> do
          addRangePred (valueExpr bnds y) (mkLowerBound (typeWidth y) (fromInteger c))
      | otherwise -> do
          when (c == 0) $ Left "0 <= x cannot be false"
          addRangePred (valueExpr bnds y) (mkUpperBound (typeWidth y) (fromInteger (c-1)))
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

-- | Maps bound expression that have been visited to their location.
--
-- We memoize expressions seen so that we can infer when two locations
-- must be equal.
type NextBlockState arch ids = MapF (BoundExpr arch ids) (BoundLoc (ArchReg arch) )

-- | Return the constraint associated with the given location and expression
-- or nothing if the constraint is the top one and should be stored.
nextStateLocConstraint :: ( MemWidth (ArchAddrWidth arch)
                          , HasRepr (ArchReg arch) TypeRepr
                          , OrdF (ArchReg arch)
                          , ShowF (ArchReg arch)
                          )
                       => LocMap (ArchReg arch) (LocConstraint (ArchReg arch))
                       -- ^ Constraints on stacks/registers
                       -> BranchConstraints (ArchReg arch) ids
                       -- ^ Bounds on assignments inferred from branch
                       -- predicate.
                       -> BoundLoc (ArchReg arch) tp
                          -- ^ Location expression is stored at.
                       -> BoundExpr arch ids tp
                          -- ^ Expression to infer predicate or.
                       -> State (NextBlockState arch ids)
                                (Maybe (LocConstraint (ArchReg arch) tp))
nextStateLocConstraint lm brCns loc e = do
  m <- get
  case MapF.lookup e m of
    Just l -> do
      pure $! Just $ EqualValue l
    Nothing -> do
      put $! MapF.insert e loc m
      case exprPred lm brCns e of
        TopPred -> pure Nothing
        p -> pure $! (Just $! ValueRep p)

nextRegConstraint :: ( MemWidth (ArchAddrWidth arch)
                     , HasRepr (ArchReg arch) TypeRepr
                     , OrdF (ArchReg arch)
                     , ShowF (ArchReg arch)
                     )
                  => IntraJumpBounds arch ids
                  -- ^ Bounds at end of this state.
                  -> BranchConstraints (ArchReg arch) ids
                  -- ^ Constraints inferred from branch (or `emptyBranchConstraints)
                  -> ArchReg arch tp
                  -> Value arch ids tp
                  -> State (NextBlockState arch ids)
                           (Maybe (LocConstraint (ArchReg arch) tp))
nextRegConstraint bnds brCns r v =
  nextStateLocConstraint (initBounds bnds) brCns (RegLoc r) (valueExpr bnds v)

nextStackConstraint :: ( MemWidth (ArchAddrWidth arch)
                       , HasRepr (ArchReg arch) TypeRepr
                       , OrdF (ArchReg arch)
                       , ShowF (ArchReg arch)
                       )
                    => IntraJumpBounds arch ids
                    -- ^ Bounds at end of this state.
                    -> BranchConstraints (ArchReg arch) ids
                    -- ^ Constraints inferred from branch (or `emptyBranchConstraints)
                    -> MemInt (ArchAddrWidth arch)
                    -> MemRepr tp
                    -> BoundExpr arch ids tp
                    -> State (NextBlockState arch ids) (Maybe (LocConstraint (ArchReg arch) tp))
nextStackConstraint bnds brCns i repr e =
  nextStateLocConstraint (initBounds bnds) brCns (StackOffLoc i repr) e

-- | Bounds for block after jump
nextBlockBounds' :: forall arch ids
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids
                   -- ^ Bounds at end of this state.
                -> BranchConstraints (ArchReg arch) ids
                   -- ^ Constraints inferred from branch (or `emptyBranchConstraints)
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitJumpBounds arch
nextBlockBounds' bnds brCns regs = do
  flip evalState MapF.empty $ do
    rm <- MapF.traverseMaybeWithKey (nextRegConstraint bnds brCns) (regStateMap regs)
    sm <- stackMapTraverseMaybeWithKey (nextStackConstraint bnds brCns) (stackExprMap bnds)
    let m = LocMap { locMapRegs = rm, locMapStack = sm }
    pure $! InitJumpBounds m

-- | Bounds for block after jump
nextBlockBounds :: forall arch ids
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids
                   -- ^ Bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitJumpBounds arch
nextBlockBounds bnds regs = nextBlockBounds' bnds emptyBranchConstraints regs

-- | Get bounds for start of block after a branch (either the true or
-- false branch)
postBranchBounds
  :: RegisterInfo (ArchReg arch)
  => IntraJumpBounds arch ids -- ^ Bounds just before jump
  -> Value arch ids BoolType -- ^ Branch condition
  -> Bool -- ^ Flag indicating if branch predicate is true or false.
  -> RegState (ArchReg arch) (Value arch ids)
  -- ^ Register values at start of next state.
  -> Either String (InitJumpBounds arch)
postBranchBounds bnds c condIsTrue regs = do
  brCns <- assertPred bnds c condIsTrue
  pure (nextBlockBounds' bnds brCns regs)

-- | Get the constraint associated with a register after a call.
postCallConstraint :: RegisterInfo (ArchReg arch)
                   => CallParams (ArchReg arch)
                      -- ^ Information about calling convention.
                   -> IntraJumpBounds arch ids
                      -- ^ Bounds at end of this state.
                   -> ArchReg arch tp
                   -- ^ Register to get
                   -> Value arch ids tp
                   -- ^ Value of register at time call occurs.
                   -> State (NextBlockState arch ids) (Maybe (LocConstraint (ArchReg arch) tp))
postCallConstraint params bnds r v
  | Just Refl <- testEquality r sp_reg
  , IsStackOffset o <-
        exprPred (initBounds bnds) emptyBranchConstraints (valueExpr bnds v) = do
      let postCallPred = IsStackOffset (o+fromInteger (postCallStackDelta params))
      pure (Just (ValueRep postCallPred))
  | preserveReg params r =
      nextStateLocConstraint (initBounds bnds) emptyBranchConstraints (RegLoc r) (valueExpr bnds v)
  | otherwise =
      pure Nothing

-- | Return the index bounds after a function call.
postCallBounds :: forall arch ids
               .  ( RegisterInfo (ArchReg arch)
                  )
               => CallParams (ArchReg arch)
               -> IntraJumpBounds arch ids
               -> RegState (ArchReg arch) (Value arch ids)
               -> InitJumpBounds arch
postCallBounds params bnds regs = do
  flip evalState MapF.empty $ do
    rm <- MapF.traverseMaybeWithKey (postCallConstraint params bnds) (regStateMap regs)
    let finalStack = stackExprMap bnds
    let filteredStack =
          case valuePred bnds (getBoundValue sp_reg regs) of
            IsStackOffset spOff
              | stackGrowsDown params ->
                  let newOff = toInteger spOff + postCallStackDelta params
                   -- Keep entries at offsets above return address.
                   in stackMapDropBelow newOff finalStack
              | otherwise ->
                  let newOff = toInteger spOff + postCallStackDelta params
                      -- Keep entries whose high address is below new stack offset
                   in stackMapDropAbove newOff finalStack
            _ -> emptyStackMap
    let nextStackFn :: MemInt (ArchAddrWidth arch)
                    -> MemRepr tp
                    -> BoundExpr arch ids tp
                    -> State (NextBlockState arch ids) (Maybe (LocConstraint (ArchReg arch) tp))
        nextStackFn = nextStackConstraint bnds emptyBranchConstraints
    sm <- stackMapTraverseMaybeWithKey nextStackFn filteredStack
    let newMap = LocMap { locMapRegs = rm, locMapStack = sm }
    pure $! InitJumpBounds newMap
