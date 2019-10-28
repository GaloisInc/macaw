{-
This code associates upper bounds with parts of registers and
addresses in the stack.
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
  , assertPred
  , unsignedUpperBound
  , stackOffset
  , UpperBound(..)
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
import           Data.Functor
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Pair
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.STRef
import           Data.Word
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
-- UpperBound

-- | An upper bound on a value.
data UpperBound tp where
  -- | @IntegerUpperBound b v@ indicates the low @b@ bits of the value
  -- are at most @v@ when the bitvector is treated as an unsigned
  -- integer.
  UBVUpperBound :: (u <= w) => !(NatRepr u) -> !Natural -> UpperBound (BVType w)

------------------------------------------------------------------------
-- ClassPred

-- | This describes a constraint associated with an equivalence class
-- of registers in @InitJumpBounds@.
--
-- The first parameter is the number of bits in the
data ClassPred (w :: Nat) tp where
  -- | Value is a bitvector with the given upper bound.  The argument
  -- is the upper bound of the bitvector when interpreted as a
  -- unsigned number.
  BoundedBV :: !(UpperBound tp)
            -> ClassPred w tp
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
ppClassPred d (BoundedBV (UBVUpperBound w b)) =
  d <> text ":[" <> text (show w) <> text "] <= " <> text (show b)
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
    (BoundedBV (UBVUpperBound u x), BoundedBV (UBVUpperBound v y))
      | Just Refl <- testEquality u v ->
        markChanged (x < y) $> BoundedBV (UBVUpperBound u (max x y))
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

------------------------------------------------------------------------
-- LocConstraint

type ClassSize = Word64

-- | A constraint on a @BoundLoc
data LocConstraint r tp where
  -- | An equivalence class representative with the given number of
  -- elements.
  --
  -- In our map the number of equivalence class members should always
  -- be positive.
  ValueRep :: !(ClassPred (RegAddrWidth r) tp)
           -> !ClassSize
           -> LocConstraint r tp
  EqualValue :: !(BoundLoc r tp)
             -> LocConstraint r tp

unconstrained :: LocConstraint r tp
unconstrained = ValueRep TopPred 1

ppLocConstraint :: ShowF r => Doc -> LocConstraint r tp -> Doc
ppLocConstraint d (ValueRep p _cnt) = ppClassPred d p
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

ppStackMap :: (forall tp . Doc -> v tp -> Doc) -> StackMap w v -> Doc
ppStackMap f (SM m)
  | Map.null m = text "empty-stack-map"
  | otherwise =
      vcat $
      [ f (ppStackOff o repr) v
      | (o,MemVal repr v) <- Map.toList m
      ]

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

-- | Looks Return value (if any) at given offset and representation.
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
unsafeStackMapInsertWith :: (p tp -> p tp -> p tp)
                         -> MemInt w
                         -> MemRepr tp
                         -> p tp
                         -> StackMap w p
                         -> StackMap w p
unsafeStackMapInsertWith upd o repr v (SM m) = SM (Map.insertWith updAnn o (MemVal repr v) m)
  where updAnn _new (MemVal oldRepr valCns) =
          case testEquality repr oldRepr of
            Just Refl -> MemVal oldRepr (upd v valCns)
            Nothing -> error $ "unsafeStackMampInsertWith given overlapping memory offsets."

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

-- | This associates the location with a value in the map, and allows
-- the old value to be updated.
--
-- It is prefixed with "nonOverlap" because it doesn't guarantee that stack
-- values are non-overlapping -- the user should ensure this before calling this.
nonOverlapLocInsertWith :: OrdF r
                        => (v tp -> v tp -> v tp)
                        -> BoundLoc r tp
                        -> v tp
                        -> LocMap r v
                        -> LocMap r v
nonOverlapLocInsertWith upd (RegLoc r) v m =
  m { locMapRegs = MapF.insertWith upd r v (locMapRegs m) }
nonOverlapLocInsertWith upd (StackOffLoc off repr) v m =
  m { locMapStack = unsafeStackMapInsertWith upd off repr v (locMapStack m) }


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
ppInitJumpBounds :: forall arch . ShowF (ArchReg arch) => InitJumpBounds arch -> [Doc]
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
  let m = LocMap { locMapRegs = MapF.singleton sp_reg (ValueRep (IsStackOffset 0) 1)
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
                      , ClassSize
                      )
boundsLocationInfo bnds l =
  case locConstraint bnds l of
    EqualValue loc -> boundsLocationInfo bnds loc
    ValueRep p c -> (l, p, c)

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
    (r,_,_) -> r

-- | Increment the reference count for a class representative.
incLocCount :: OrdF (ArchReg arch)
            => BoundLoc (ArchReg arch) tp
            -> InitJumpBounds arch
            -> InitJumpBounds arch
incLocCount loc (InitJumpBounds m) =
    InitJumpBounds (nonOverlapLocInsertWith upd loc (ValueRep TopPred 2) m)
  where upd _new (ValueRep p cnt) = ValueRep p (cnt+1)
        upd _new (EqualValue _) = error $ "insLocCount given non-class representative."

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
  (oldRep, oldPred, _oldCnt) <- lift $
    case oldCns of
      ValueRep p c -> do
        -- Increment number of equivalence classes when we see an old
        -- representative.
        modifySTRef' cntr (+1)
        -- Return this loc
        pure (thisLoc, p, c)
      EqualValue  oldLoc ->
        pure (boundsLocationInfo old oldLoc)
  let (newRep, newPred, _newCnt) = boundsLocationInfo new thisLoc
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
          _ -> modifySTRef' bndsRef $ setLocConstraint thisLoc (ValueRep p 1)
    Just resRep ->
      -- Assert r is equal to resRep
      lift $ modifySTRef' bndsRef $
        incLocCount resRep . setLocConstraint thisLoc (EqualValue resRep)

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

-- | @combineUpperBound ubnd old@ returns predicate that is no
-- stronger than assumption @ubnd@ and @old@ hold.
combineUpperBound :: UpperBound (BVType w)
                  -> ClassPred a (BVType w)
                  -> ClassPred a (BVType w)
combineUpperBound ubnd oldp  =
  case oldp of
    TopPred -> BoundedBV ubnd      -- Prefer newbound.
    BoundedBV _ -> BoundedBV ubnd  -- Prefer newbound
    IsStackOffset _ -> oldp -- Prefer stackoffset

-- | Add a upper bound to a class representative
addClassRepBound :: ( HasCallStack
                    , OrdF (ArchReg arch)
                    , MemWidth (ArchAddrWidth arch)
                    )
                 => BoundLoc (ArchReg arch) (BVType w)
                 -- ^ The location to update.
                 --
                 -- This should be a class representative in the initial state.
                 -- bounds.
                 -> UpperBound (BVType w)
                 -> InitJumpBounds arch
                 -> InitJumpBounds arch
addClassRepBound l ubnd (InitJumpBounds m) =
  let p0 = ValueRep (BoundedBV ubnd) 1
      upd _ (EqualValue _) = error "addClassBounds expected class rep"
      upd _ (ValueRep oldp cnt) = ValueRep (combineUpperBound ubnd oldp) cnt
   in InitJumpBounds (locOverwriteWith upd l p0 m)

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
data BoundExpr arch ids s tp where
  -- | This refers to the contents of the location at the start
  -- of block execution.
  --
  -- The location should be a class representative in the initial bounds.
  ClassRepExpr :: !(BoundLoc (ArchReg arch) tp) -> BoundExpr arch ids s tp
  -- | An assignment that is not interpreted, and just treated as a constant.
  AssignExpr :: !(AssignId ids tp)
             -> !(TypeRepr tp)
             -> BoundExpr arch ids s tp
  -- | Denotes the value of the stack pointer at function start plus some constant.
  StackOffsetExpr :: !(MemInt (ArchAddrWidth arch))
                  -> BoundExpr arch ids s (BVType (ArchAddrWidth arch))
  -- | Denotes a constant
  CExpr :: !(CValue arch tp) -> BoundExpr arch ids s tp
  -- | This is a pure function applied to other index expressions that
  -- does not seem to be a stack offset or assignment.
  AppExpr :: !(Nonce s tp)
          -> !(App (BoundExpr arch ids s) tp)
          -> BoundExpr arch ids s tp

instance TestEquality (ArchReg arch) => TestEquality (BoundExpr arch ids s) where
  testEquality (ClassRepExpr x) (ClassRepExpr y) =
    testEquality x y
  testEquality (AssignExpr x _) (AssignExpr y _) =
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

instance OrdF (ArchReg arch) => OrdF (BoundExpr arch ids s) where
  compareF (ClassRepExpr x) (ClassRepExpr y) = compareF x y
  compareF ClassRepExpr{} _ = LTF
  compareF _ ClassRepExpr{} = GTF

  compareF (AssignExpr x _) (AssignExpr y _) = compareF x y
  compareF AssignExpr{} _ = LTF
  compareF _ AssignExpr{} = GTF


  compareF (StackOffsetExpr x) (StackOffsetExpr y) = fromOrdering (compare x y)
  compareF StackOffsetExpr{} _ = LTF
  compareF _ StackOffsetExpr{} = GTF

  compareF (CExpr x) (CExpr y) = compareF x y
  compareF CExpr{} _ = LTF
  compareF _ CExpr{} = GTF

  compareF (AppExpr xn _xa) (AppExpr yn _ya) = compareF xn yn

instance ( HasRepr (ArchReg arch) TypeRepr
         , MemWidth (ArchAddrWidth arch)
         ) => HasRepr (BoundExpr arch ids s) TypeRepr where
  typeRepr e =
    case e of
      ClassRepExpr x    -> typeRepr x
      AssignExpr _ tp   -> tp
      StackOffsetExpr _ -> addrTypeRepr
      CExpr x           -> typeRepr x
      AppExpr _ a       -> typeRepr a

-- | Return an expression equivalent to the location in the bounds.
--
-- This attempts to normalize the expression to get a representative.
locExpr :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
        => InitJumpBounds arch
        -> BoundLoc (ArchReg arch) tp
        -> BoundExpr arch ids s tp
locExpr bnds loc =
  case boundsLocationInfo bnds loc of
    (_, IsStackOffset i, _) -> StackOffsetExpr i
    (rep, BoundedBV _, _) -> ClassRepExpr rep
    (rep, TopPred, _) -> ClassRepExpr rep

------------------------------------------------------------------------
-- IntraJumpBounds

-- | Information about bounds for a particular value within a block.
data IntraJumpBounds arch ids s
   = IntraJumpBounds { initBounds :: !(InitJumpBounds arch)
                       -- ^ Initial bounds at execution start.
                     , stackExprMap :: !(StackMap (ArchAddrWidth arch) (BoundExpr arch ids s))
                        -- ^ Maps stack offsets to the expression associated with them.
                     , assignExprMap :: !(MapF (AssignId ids) (BoundExpr arch ids s))
                       -- ^ Maps processed assignments to index expressions.
                     , assignBoundMap :: !(MapF (AssignId ids) UpperBound)
                       -- ^ Maps assignments to any asserted upper bound infor,ation.
                     , appBoundMap :: !(MapF (Nonce s) UpperBound)
                       -- ^ Maps app expression nonce to the upper bound.
                     , memoTable :: !(MapF (App (BoundExpr arch ids s)) (BoundExpr arch ids s))
                       -- ^ Table for ensuring each bound expression
                       -- has a single representative.
                     }

-- | Create index bounds from initial index bounds.
mkIntraJumpBounds :: forall arch ids s
                  .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => InitJumpBounds arch
                  -> IntraJumpBounds arch ids s
mkIntraJumpBounds initBnds = do
  let -- Map stack offset and memory annotation pair to the
      -- representative in the initial bounds.
      stackExpr :: MemInt (ArchAddrWidth arch)
                -> MemRepr tp
                -> LocConstraint (ArchReg arch) tp
                -> BoundExpr arch ids s tp
      stackExpr i tp _ = locExpr initBnds (StackOffLoc i tp)
   in IntraJumpBounds { initBounds     = initBnds
                      , stackExprMap   = stackMapMapWithKey stackExpr (locMapStack (initBndsMap initBnds))
                      , assignExprMap  = MapF.empty
                      , assignBoundMap = MapF.empty
                      , appBoundMap    = MapF.empty
                      , memoTable      = MapF.empty
                      }

-- | Return the value of the index expression given the bounds.
valueExpr :: forall arch ids s tp
          .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
          => IntraJumpBounds arch ids s
          -> Value arch ids tp
          -> BoundExpr arch ids s tp
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
            => IntraJumpBounds arch ids s
            -> Value arch ids (BVType (ArchAddrWidth arch))
            -> Maybe (MemInt (ArchAddrWidth arch))
stackOffset bnds val =
  case valueExpr bnds val of
    StackOffsetExpr i -> Just i
    _ -> Nothing

bindAssignment :: IntraJumpBounds arch ids s
              -> AssignId ids tp
              -> BoundExpr arch ids s tp
              -> IntraJumpBounds arch ids s
bindAssignment bnds aid expr =
  bnds { assignExprMap = MapF.insert aid expr (assignExprMap bnds) }

-- | Update the stack to point to the given expression.
writeStackOff :: forall arch ids s tp
              .  MemWidth (ArchAddrWidth arch)
              => IntraJumpBounds arch ids s
              -> MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> BoundExpr arch ids s tp
              -> IntraJumpBounds arch ids s
writeStackOff bnds off repr v =
  bnds { stackExprMap = stackMapOverwrite off repr v (stackExprMap bnds) }

-- | Return an index expression associated with the @AssignRhs@.
rhsExpr :: forall arch ids s tp
        .  ( MemWidth (ArchAddrWidth arch)
           , OrdF (ArchReg arch)
           )
        => NonceGenerator (ST s) s
        -> IntraJumpBounds arch ids s
        -> AssignId ids tp
        -> AssignRhs arch (Value arch ids) tp
        -> ST s (BoundExpr arch ids s tp)
rhsExpr gen bnds aid arhs =
  case arhs of
    EvalApp app -> do
      let stackFn v = toInteger <$> stackOffset bnds v
      case appAsStackOffset stackFn app of
        Just (StackOffsetView o) -> do
          pure $ StackOffsetExpr $ fromInteger o
        _ -> do
          let a = fmapFC (valueExpr bnds) app
          case MapF.lookup a (memoTable bnds) of
            Just r -> do
              pure r
            Nothing -> do
              (`AppExpr` a) <$> freshNonce gen
    ReadMem addr repr
      | Just o <- stackOffset bnds addr
      , SMLResult e <- stackMapLookup o repr (stackExprMap bnds) -> do
          pure e
    _ -> do
      pure $! AssignExpr aid (typeRepr arhs)

-- | Given a statement this modifies the bounds based on the statement.
execStatement :: ( MemWidth (ArchAddrWidth arch)
                 , OrdF (ArchReg arch)
                 )
              => NonceGenerator (ST s) s
              -> IntraJumpBounds arch ids s
              -> Stmt arch ids
              -> ST s (IntraJumpBounds arch ids s)
execStatement gen bnds stmt =
  case stmt of
    AssignStmt (Assignment aid arhs) -> do
      let bnds' = case arhs of
                    EvalArchFn{} -> bnds { stackExprMap = emptyStackMap }
                    _ -> bnds
      bindAssignment bnds' aid <$> rhsExpr gen bnds' aid arhs
    WriteMem addr repr val ->
      case stackOffset bnds addr of
        Just addrOff ->
          pure $! writeStackOff bnds addrOff repr (valueExpr bnds val)
        -- If we write to something other than stack, then clear all stack references.
        Nothing ->
          pure $! bnds { stackExprMap = emptyStackMap }
    CondWriteMem{} -> pure $! bnds { stackExprMap = emptyStackMap }
    InstructionStart{} -> pure $! bnds
    Comment{} -> pure $! bnds
    ExecArchStmt{} -> pure $! bnds { stackExprMap = emptyStackMap }
    ArchState{} -> pure $! bnds

instance ShowF (ArchReg arch) => Pretty (IntraJumpBounds arch ids s) where
  pretty bnds = pretty (initBounds bnds)

------------------------------------------------------------------------
-- Operations

cvaluePred :: CValue arch tp -> ClassPred (ArchAddrWidth arch) tp
cvaluePred v =
  case v of
    BoolCValue _ -> TopPred
    BVCValue w i -> BoundedBV (UBVUpperBound w (fromInteger i))
    RelocatableCValue{} -> TopPred
    SymbolCValue{} -> TopPred


exprPred :: ( MemWidth (ArchAddrWidth arch)
            , HasRepr (ArchReg arch) TypeRepr
            , OrdF (ArchReg arch)
            )
         => IntraJumpBounds arch ids s
         -> BoundExpr arch ids s tp
         -> ClassPred (ArchAddrWidth arch) tp
exprPred bnds v =
  case v of
    ClassRepExpr loc ->
      case boundsLocationInfo (initBounds bnds) loc of
        (_,p,_) -> p
    AssignExpr n _ -> do
      case MapF.lookup n (assignBoundMap bnds) of
        Just b  -> BoundedBV b
        Nothing -> TopPred
    StackOffsetExpr x -> IsStackOffset x
    CExpr c -> cvaluePred c
    AppExpr n _app
      | Just b <- MapF.lookup n (appBoundMap bnds) ->
          BoundedBV b
    AppExpr _n app ->
      case app of
        BVAnd _ x y ->
          case (exprPred bnds x,  exprPred bnds y) of
            (BoundedBV (UBVUpperBound xw xb), BoundedBV (UBVUpperBound yw yb))
              | Just Refl <- testEquality xw yw ->
                  BoundedBV (UBVUpperBound xw (min xb yb))
            (TopPred, yb) -> yb
            (xb, _)       -> xb
        SExt x w ->
          case exprPred bnds x of
            BoundedBV (UBVUpperBound u b) ->
              case testLeq u w of
                Just LeqProof -> BoundedBV (UBVUpperBound u b)
                Nothing -> error "unsignedUpperBound given bad width"
            _ -> TopPred
        UExt x w ->
          case exprPred bnds x of
            BoundedBV (UBVUpperBound u r) ->
              -- If bound is full width, then we can keep it, otherwise we only have subset.
              case testEquality u (typeWidth x) of
                Just Refl -> BoundedBV (UBVUpperBound w r)
                Nothing ->
                  case testLeq u w of
                    Just LeqProof -> BoundedBV (UBVUpperBound u r)
                    Nothing -> error "unsignedUpperBound given bad width"
            _ -> TopPred
        Trunc x w ->
          case exprPred bnds x of
            BoundedBV (UBVUpperBound u xr) -> BoundedBV $
              case testLeq u w of
                Just LeqProof -> do
                  UBVUpperBound u xr
                Nothing -> do
                  UBVUpperBound w (min xr (fromInteger (maxUnsigned w)))
            _ -> TopPred
        _ -> TopPred

-- | This attempts to resolve the predicate associated with a value.
valuePred :: ( MapF.OrdF (ArchReg arch)
             , MapF.ShowF (ArchReg arch)
             , RegisterInfo (ArchReg arch)
             )
          => IntraJumpBounds arch ids s
          -> Value arch ids tp
          -> ClassPred (ArchAddrWidth arch) tp
valuePred bnds v =
  case v of
    CValue cv -> cvaluePred cv
    AssignedValue a ->
      case MapF.lookup (assignId a) (assignExprMap bnds) of
        Just valExpr -> exprPred bnds valExpr
        Nothing -> TopPred
    Initial r ->
      case boundsLocationInfo (initBounds bnds) (RegLoc r) of
        (_,p,_) -> p

-- | Lookup an upper bound or return analysis for why it is not defined.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => IntraJumpBounds arch ids s
                   -> Value arch ids tp
                   -> Either String (UpperBound tp)
unsignedUpperBound bnds v =
  case valuePred bnds v of
    BoundedBV b -> Right b
    _ -> Left $ "Value has no upper bound."

-- | Add a inclusive upper bound to a value.
--
-- Our operation allows one to set the upper bounds on the low order
-- of an integer.  This is represented by the extra argument `NatRepr
-- u`.
--
-- This either returns the refined bounds, or `Left msg` where `msg`
-- is an explanation of what inconsistency was detected.  The upper
-- bounds must be non-negative.
addUpperBound :: ( MapF.OrdF (ArchReg arch)
                 , HasRepr (ArchReg arch) TypeRepr
                 , u <= w
                 , MemWidth (ArchAddrWidth arch)
                 )
               => BoundExpr arch ids s (BVType w)
                 -- ^ Value we are adding upper bound for.
               -> NatRepr u
                  -- ^ Restrict upper bound to only `u` bits.
               -> Natural
               -- ^ Upper bound as an unsigned number
               -> IntraJumpBounds arch ids s
                 -- ^ Current bounds.
               -> Either String (IntraJumpBounds arch ids s)
addUpperBound v _u bnd bnds
    -- Do nothing if upper bounds equals or exceeds maximum unsigned
    -- value.
  | bnd >= fromInteger (maxUnsigned (typeWidth v)) = Right bnds
addUpperBound v u bnd bnds =
  case v of
    ClassRepExpr loc ->
      pure $ bnds { initBounds = addClassRepBound loc (UBVUpperBound u bnd) (initBounds bnds) }
    AssignExpr aid _ -> do
      pure $ bnds { assignBoundMap = MapF.insert aid (UBVUpperBound u bnd) (assignBoundMap bnds) }
    StackOffsetExpr _i ->
      Right bnds
    CExpr cv ->
      case cv of
        BVCValue _ c | c <= toInteger bnd -> Right bnds
                     | otherwise -> Left "Constant given upper bound that is statically less than given bounds"
        RelocatableCValue{} -> Right bnds
        SymbolCValue{}      -> Right bnds
    AppExpr n a ->
      case a of
        UExt x _ ->
          case testLeq u (typeWidth x) of
            Just LeqProof -> addUpperBound x u bnd bnds
            Nothing ->
              case leqRefl (typeWidth x) of
                LeqProof -> addUpperBound x (typeWidth x) bnd bnds
        Trunc x w ->
            case testLeq u w of
              Just LeqProof -> do
                case testLeq u (typeWidth x) of
                  Just LeqProof -> addUpperBound x u bnd bnds
                  Nothing -> error "addUpperBound invariant broken"
              Nothing -> do
                case testLeq w (typeWidth x) of
                  Just LeqProof -> addUpperBound x w bnd bnds
                  Nothing -> error "addUpperBound invariant broken"
        _ ->
            Right $ bnds { appBoundMap =
                             MapF.insert n (UBVUpperBound u bnd) (appBoundMap bnds)
                         }

-- | Assert a predicate is true/false and update bounds.
--
-- If it returns a new upper bounds, then that may be used.
-- Otherwise, it detects an inconsistency and returns a message
-- explaing why.
assertPred :: ( OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              , MemWidth (ArchAddrWidth arch)
              )
           => Value arch ids BoolType -- ^ Value representing predicate
           -> Bool -- ^ Controls whether predicate is true or false
           -> IntraJumpBounds arch ids s -- ^ Current index bounds
           -> Either String (IntraJumpBounds arch ids s)
assertPred (AssignedValue a) isTrue bnds =
  case assignRhs a of
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c))
      | isTrue     ->
        if c > 0 then
          addUpperBound (valueExpr bnds x) (typeWidth x) (fromInteger (c-1)) bnds
         else
          Left "x < 0 must be false."
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue _ c) y)
      | not isTrue -> addUpperBound (valueExpr bnds y) (typeWidth y) (fromInteger c) bnds
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue _ c))
      | isTrue     -> addUpperBound (valueExpr bnds x) (typeWidth x) (fromInteger c) bnds
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y) | not isTrue ->
      if c > 0 then
        addUpperBound (valueExpr bnds y) (typeWidth y) (fromInteger (c-1)) bnds
       else
        Left "0 <= x cannot be false"
    -- Given x && y, assert x, then assert y
    EvalApp (AndApp l r) | isTrue     -> (assertPred l True >=> assertPred r True) bnds
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) | not isTrue -> (assertPred l False >=> assertPred r False) bnds
    EvalApp (NotApp p) -> assertPred p (not isTrue) bnds
    _ -> Right bnds
assertPred _ _ bnds = Right bnds

-- | Maps bound expression that have been visited to their location.
--
-- We memoize expressions seen so that we can infer when two locations must be equal.
type NextBlockState arch ids s = MapF (BoundExpr arch ids s) (BoundLoc (ArchReg arch) )

-- | Return the constraint associated with the given location and expression
-- or nothing if the constraint is the top one and should be stored.
nextStateLocConstraint :: ( MemWidth (ArchAddrWidth arch)
                          , HasRepr (ArchReg arch) TypeRepr
                          , OrdF (ArchReg arch)
                          )
                       => IntraJumpBounds arch ids s
                       -- ^ Bounds at end of this state.
                       -> BoundLoc (ArchReg arch) tp
                          -- ^ Location expression is stored at.
                       -> BoundExpr arch ids s tp
                          -- ^ Expression to infer predicate or.
                       -> State (NextBlockState arch ids s)
                                (Maybe (LocConstraint (ArchReg arch) tp))
nextStateLocConstraint bnds loc e = do
  m <- get
  case MapF.lookup e m of
    Just l -> do
      -- Question: Shouldn't I increment count for l?
      pure $! Just $ EqualValue l
    Nothing -> do
      put $! MapF.insert e loc m
      case exprPred bnds e of
        TopPred -> pure Nothing
        p -> pure $! (Just $! ValueRep p 1)

nextRegConstraint :: ( MemWidth (ArchAddrWidth arch)
                     , HasRepr (ArchReg arch) TypeRepr
                     , OrdF (ArchReg arch)
                     )
                  => IntraJumpBounds arch ids s
                  -- ^ Bounds at end of this state.
                  -> ArchReg arch tp
                  -> Value arch ids tp
                  -> State (NextBlockState arch ids s) (Maybe (LocConstraint (ArchReg arch) tp))
nextRegConstraint bnds r v = nextStateLocConstraint bnds (RegLoc r) (valueExpr bnds v)

nextStackConstraint :: ( MemWidth (ArchAddrWidth arch)
                       , HasRepr (ArchReg arch) TypeRepr
                       , OrdF (ArchReg arch)
                       )
                    => IntraJumpBounds arch ids s
                    -- ^ Bounds at end of this state.
                    -> MemInt (ArchAddrWidth arch)
                    -> MemRepr tp
                    -> BoundExpr arch ids s tp
                    -> State (NextBlockState arch ids s) (Maybe (LocConstraint (ArchReg arch) tp))
nextStackConstraint bnds i repr e =
  nextStateLocConstraint bnds (StackOffLoc i repr) e

-- | Bounds for block after jump
nextBlockBounds :: forall arch ids s
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids s
                   -- ^ Bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitJumpBounds arch
nextBlockBounds bnds regs = do
  flip evalState MapF.empty $ do
    rm <- MapF.traverseMaybeWithKey (nextRegConstraint bnds) (regStateMap regs)
    sm <- stackMapTraverseMaybeWithKey (nextStackConstraint bnds) (stackExprMap bnds)
    let m = LocMap { locMapRegs = rm, locMapStack = sm }
    pure $! InitJumpBounds m

-- | Get the constraint associated with a register after a call.
postCallConstraint :: RegisterInfo (ArchReg arch)
                   => CallParams (ArchReg arch)
                      -- ^ Information about calling convention.
                   -> IntraJumpBounds arch ids s
                      -- ^ Bounds at end of this state.
                   -> ArchReg arch tp
                   -- ^ Register to get
                   -> Value arch ids tp
                   -- ^ Value of register at time call occurs.
                   -> State (NextBlockState arch ids s) (Maybe (LocConstraint (ArchReg arch) tp))
postCallConstraint params bnds r v
  | Just Refl <- testEquality r sp_reg
  , IsStackOffset o <- exprPred bnds (valueExpr bnds v) = do
      let postCallPred = IsStackOffset (o+fromInteger (postCallStackDelta params))
      pure (Just (ValueRep postCallPred 1))
  | preserveReg params r =
      nextStateLocConstraint bnds (RegLoc r) (valueExpr bnds v)
  | otherwise =
      pure Nothing

-- | Return the index bounds after a function call.
postCallBounds :: forall arch ids s
               .  ( RegisterInfo (ArchReg arch)
                  )
               => CallParams (ArchReg arch)
               -> IntraJumpBounds arch ids s
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
    sm <- stackMapTraverseMaybeWithKey (nextStackConstraint bnds) filteredStack
    let newMap = LocMap { locMapRegs = rm, locMapStack = sm }
    pure $! InitJumpBounds newMap
