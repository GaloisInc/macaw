{- |

This module defines a relational abstract domain for tracking
registers and stack addresses.  The model records when one of these
values is known to be equal to the current pointer stack frame.  This
domain also tracks equalities between nodes so that analysis
algorithms built on top of this are modulo known equivalences
between registers and stack locations.

The theory is defined over bitvector with a predefined
"address width" @addrWidth@ for the number of bits in the
address space

> p := t = u
>   |  t = stack_frame + c
>   |  t = uext u w    (1 <= width u && width u < w)
>
> t := r (@r@ is a register)
>   |  *(stack_frame + c)

@c@ is a signed @addrWidth@-bit bitvector.  @stack_frame@ denotes
a @addrWidth@-bit bitvector for the stack frame.  @w@ is a width
parameter.

Given a set of axioms using the constraint @P@ we have the following
proof rules:

> A,p |= p                                                       (assumption)
> A   |= t = t                                                   (reflexivity)
> A   |= t = u => A |= u = t                                     (symmetry)
> A   |= t = u && A |= u = v => A |= t = v                       (transitivity)
> A   |= t = uext u w && A |= u = uext v w' => A |= t = uext v w (double uext)
> A   |= t = uext u w && A |= u = v => A |= t = uext v w         (uext congruence)

-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.AbsDomain.StackAnalysis
  ( -- * Block level datatypes
    -- ** BlockStartStackConstraints
    BlockStartStackConstraints
  , StackEqConstraint(..)
  , ppBlockStartStackConstraints
  , fnEntryBlockStartStackConstraints
  , ppStackEqConstraint
  , blockStartLocExpr
  , blockStartLocStackOffset
  , StackOffConstraint(..)
  , blockStartLocRepAndCns
  , BoundLoc(..)
  , joinBlockStartStackConstraints
  , JoinClassMap
  , JoinClassPair(..)
    -- ** BlockIntraStackConstraints
  , BlockIntraStackConstraints
  , mkBlockIntraStackConstraints
  , biscInitConstraints
  , intraStackValueExpr
  , StackExpr(..)
  , intraStackRhsExpr
  , intraStackSetAssignId
  , discardMemInfo
  , writeStackOff
    -- ** Block terminator updates
  , postJumpStackConstraints
  , Data.Macaw.AbsDomain.CallParams.CallParams
  , postCallStackConstraints
    -- * LocMap
  , LocMap(..)
  , locMapEmpty
  , locMapNull
  , locMapToList
  , locLookup
  , nonOverlapLocInsert
  , locOverwriteWith
  , ppLocMap
  , foldLocMap
    -- * MemMap
  , MemMap
  , emptyMemMap
  , memMapLookup
  , MemMapLookup(..)
  , memMapOverwrite
  , memMapMapWithKey
  , memMapTraverseWithKey_
  , memMapTraverseMaybeWithKey
  , memMapDropAbove
  , memMapDropBelow
    -- * NextStateMonad
  , NextStateMonad
  , runNextStateMonad
  , getNextStateRepresentatives
    -- * Miscelaneous
  , MemVal(..)
  ) where

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Pair
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.Proxy
import           Data.STRef
import           GHC.Natural
import           Prettyprinter
import           Text.Printf

import           Data.Macaw.AbsDomain.CallParams
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import qualified Data.Macaw.Types as M
import           Data.Macaw.Types hiding (Type)
import           Data.Macaw.Utils.Changed

addrTypeRepr :: MemWidth w => TypeRepr (BVType w)
addrTypeRepr = BVTypeRepr memWidthNatRepr

ppAddend :: MemInt w -> Doc ann
ppAddend o | memIntValue o < 0 =
               "-" <+> pretty (negate (toInteger (memIntValue o)))
           | otherwise = "+" <+> pretty o

ppStackOff :: MemInt w -> MemRepr tp -> Doc ann
ppStackOff o repr =
  "*(stack_frame" <+> ppAddend o <> ", " <> pretty repr <> ")"

------------------------------------------------------------------------
-- JoinClassPair

data JoinClassPair (key :: k -> Type)  (tp :: k) = JoinClassPair !(key tp) !(key tp)

instance TestEquality k => TestEquality (JoinClassPair k) where
  testEquality (JoinClassPair x1 x2) (JoinClassPair y1 y2) = do
    Refl <- testEquality x1 y1
    testEquality x2 y2

instance OrdF k => OrdF (JoinClassPair k) where
  compareF (JoinClassPair x1 x2) (JoinClassPair y1 y2) =
    joinOrderingF (compareF x1 y1) (compareF x2 y2)

------------------------------------------------------------------------
-- MemVal

-- | A value with a particular type along with a MemRepr indicating
-- how the type is encoded in memory.
data MemVal (p :: M.Type -> Type) =
  forall (tp :: M.Type) . MemVal !(MemRepr tp) !(p tp)

instance FunctorF MemVal where
  fmapF f (MemVal r x) = MemVal r (f x)

------------------------------------------------------------------------
-- BoundLoc

-- | A location within a function tracked by our bounds analysis
-- algorithms.
--
-- Locations for these purposes are registers, stack offsets, and
-- global memory offsets.
data BoundLoc (r :: M.Type -> Type) (tp :: M.Type) where
  -- | @RegLoc r@ denotes the register @r@.
  RegLoc :: !(r tp) -> BoundLoc r tp
  -- | @StackkOffLoc o repr@ denotes the bytes from address range
  -- @[initSP + o .. initSP + o + memReprBytes repr)@.
  --
  -- @initSP@ denotes the stack offset at the start of function
  -- execution.
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
  pretty (RegLoc r) = pretty (showF r)
  pretty (StackOffLoc i tp) = ppStackOff i tp

instance ShowF r => PrettyF (BoundLoc r) where
  prettyF = pretty

instance ShowF r => Show (BoundLoc r tp) where
  show = show . pretty

instance ShowF r => ShowF (BoundLoc r)

instance TestEquality r => Eq (BoundLoc r tp) where
  x == y = isJust (testEquality x y)

------------------------------------------------------------------------
-- MemMap

-- | This is a data structure for representing values written to
-- concrete offsets in memory.
--
-- The offset type is a parameter so that we can use signed or
-- unsigned offsets.
newtype MemMap o (v :: M.Type -> Type) = SM (Map o (MemVal v))

instance FunctorF (MemMap o) where
  fmapF f (SM m) = SM (fmap (fmapF f) m)

-- | Empty stack map
emptyMemMap :: MemMap o v
emptyMemMap = SM Map.empty

memMapNull :: MemMap o v -> Bool
memMapNull (SM m) = Map.null m

-- | Result returned by @memMapLookup@.
data MemMapLookup o p tp where
  -- | We found a value at the exact offset and repr
  MMLResult :: !(p tp) -> MemMapLookup o p tp
  -- | We found a value that had an overlapping offset and repr.
  MMLOverlap  :: !o
              -> !(MemRepr utp)
              -> !(p utp)
              -> MemMapLookup o p tp
  -- | We found neither an exact match nor an overlapping write.
  MMLNone :: MemMapLookup o p tp

class Ord o => MemIndex o where
  -- | @endOffset o w@ returns @Just (o + w)@ if it can be computed
  -- without overflowing.
  endOffset :: o -> Natural -> Maybe o

  -- | @memOverlap b r i@ returns @True@ if @b <= i@ and
  -- @i - b < sizeOf r@.
  memOverlap :: o -> MemRepr tp -> o -> Bool

instance MemWidth w => MemIndex (MemInt w) where
  endOffset off sz | toInteger endI == end = Just endI
                   | otherwise = Nothing
    where end = toInteger off + toInteger sz
          endI = fromIntegral end
  memOverlap b r i
    = b <= i
    && toInteger (memIntValue i)
       <  toInteger (memIntValue b) + toInteger (memReprBytes r)

instance MemWidth w => MemIndex (MemWord w) where
  endOffset off sz | fromIntegral endI == end = Just endI
                   | otherwise = Nothing
    where end = fromIntegral off + sz
          endI = fromIntegral end
  memOverlap b r i
    = memWordValue b <= memWordValue i
    && fromIntegral (memWordValue i - memWordValue b) < memReprBytes r


-- | Lookup value (if any) at given offset and representation.
memMapLookup :: MemIndex o
             => o
             -> MemRepr tp
             -> MemMap o p
             -> MemMapLookup o p tp
memMapLookup off repr (SM m) =  do
  case endOffset off (memReprBytes repr) of
    Nothing -> MMLNone
    Just end ->
      case Map.lookupLT end m of
        Nothing -> MMLNone
        Just (oldOff, MemVal oldRepr val)
          -- If match exact
          | oldOff == off
          , Just Refl <- testEquality oldRepr repr ->
          MMLResult val
          -- If previous write ends after this write starts
          | memOverlap oldOff oldRepr off ->
            MMLOverlap oldOff oldRepr val
          | otherwise ->
            MMLNone

-- | This assigns a region of bytes to a particular value in the stack.
--
-- It overwrites any values that overlap with the location.
memMapOverwrite :: forall o p tp
                .  (Ord o, Num o)
                => o -- ^ Offset in the stack to write to
                -> MemRepr tp -- ^ Type of value to write
                -> p tp  -- ^ Value to write
                -> MemMap o p
                -> MemMap o p
memMapOverwrite off repr v (SM m) =
   let e = off + fromIntegral (memReprBytes repr) - 1
       (lm, _) = Map.split off m
       hm | off <= e = snd (Map.split e m)
          | otherwise = Map.empty
    in SM $ Map.insert off (MemVal repr v) lm <> hm

-- | This sets the value at an offset without checking to clear any
-- previous writes to values.
unsafeMemMapInsert :: Ord o => o -> MemRepr tp -> p tp -> MemMap o p -> MemMap o p
unsafeMemMapInsert o repr v (SM m) = SM (Map.insert o (MemVal repr v) m)

memMapFoldlWithKey :: (forall tp . r -> o -> MemRepr tp -> v tp -> r)
                   -> r
                   -> MemMap o v
                   -> r
memMapFoldlWithKey f z (SM m) =
  Map.foldlWithKey (\r k (MemVal repr v) -> f r k repr v) z m

memMapFoldrWithKey :: (forall tp . o -> MemRepr tp -> v tp -> r -> r)
                   -> r
                   -> MemMap o v
                   -> r
memMapFoldrWithKey f z (SM m) =
  Map.foldrWithKey (\k (MemVal repr v) r -> f k repr v r) z m

memMapTraverseWithKey_ :: Applicative m
                       => (forall tp . o -> MemRepr tp -> v tp -> m ())
                       -> MemMap o v
                       -> m ()
memMapTraverseWithKey_ f (SM m) =
  Map.foldrWithKey (\k (MemVal repr v) r -> f k repr v *> r) (pure ()) m

memMapMapWithKey :: (forall tp . o -> MemRepr tp -> a tp -> b tp)
                 -> MemMap o a
                 -> MemMap o b
memMapMapWithKey f (SM m) =
  SM (Map.mapWithKey (\o (MemVal repr v) -> MemVal repr (f o repr v)) m)

memMapTraverseMaybeWithKey
  :: Applicative m
  => (forall tp . o -> MemRepr tp -> a tp -> m (Maybe (b tp)))
  -- ^ Traversal function
  -> MemMap o a
  -> m (MemMap o b)
memMapTraverseMaybeWithKey f (SM m) =
  SM <$> Map.traverseMaybeWithKey
       (\o (MemVal repr v) -> fmap (MemVal repr) <$> f o repr v) m

-- @memMapDropAbove bnd m@ includes only entries in @m@ whose bytes
-- do not go above @bnd@.
memMapDropAbove :: Integral o => Integer -> MemMap o p -> MemMap o p
memMapDropAbove bnd (SM m) = SM (Map.filterWithKey p m)
  where p o (MemVal r _) = toInteger o  + toInteger (memReprBytes r) <= bnd

-- @memMapDropBelow bnd m@ includes only entries in @m@ whose bytes
-- do not go below @bnd@.
memMapDropBelow :: Integral o => Integer -> MemMap o p -> MemMap o p
memMapDropBelow bnd (SM m) = SM (Map.filterWithKey p m)
  where p o _ = toInteger o >= bnd

------------------------------------------------------------------------
-- LocMap

-- | A map from `BoundLoc` locations to values.
data LocMap (r :: M.Type -> Type) (v :: M.Type -> Type)
  = LocMap { locMapRegs :: !(MapF r v)
           , locMapStack :: !(MemMap (MemInt (RegAddrWidth r)) v)
           }

-- | Return true if map is null.
locMapNull :: LocMap r v -> Bool
locMapNull m
  = MapF.null (locMapRegs m)
  && memMapNull (locMapStack m)

-- | An empty location map.
locMapEmpty :: LocMap r v
locMapEmpty = LocMap { locMapRegs  = MapF.empty
                     , locMapStack = emptyMemMap
                     }

-- | Construct a list out of a location map.
locMapToList :: forall r v . LocMap r v -> [Pair (BoundLoc r) v]
locMapToList m0 =
  let prependRegPair r v z = Pair (RegLoc r) v : z
      prependStackPair i repr v z = Pair (StackOffLoc i repr) v : z
   in flip (MapF.foldrWithKey prependRegPair) (locMapRegs m0) $
      flip (memMapFoldrWithKey prependStackPair) (locMapStack m0) $
      []

-- | Fold over values in a location map.
foldLocMap :: forall a r v
           .  (forall tp . a -> BoundLoc r tp -> v tp -> a)
           -> a
           -> LocMap r v
           -> a
foldLocMap f a0 m0 =
  flip (memMapFoldlWithKey (\a o r v -> f a (StackOffLoc o r) v)) (locMapStack m0) $
  flip (MapF.foldlWithKey (\a r v -> f a (RegLoc r) v)) (locMapRegs m0) a0

locMapTraverseWithKey_ :: forall m r p
                       .  Applicative m
                       => (forall tp . BoundLoc r tp -> p tp -> m ())
                       -> LocMap r p
                       -> m ()
locMapTraverseWithKey_ f m0 = do
  let regFn :: r utp -> p utp -> m ()
      regFn r v = f (RegLoc r) v
      stackFn :: MemInt (RegAddrWidth r) -> MemRepr utp -> p utp -> m ()
      stackFn o r c = f (StackOffLoc o r) c
  MapF.traverseWithKey_ regFn (locMapRegs m0)
   *> memMapTraverseWithKey_ stackFn (locMapStack m0)

-- | Pretty print a location map.
ppLocMap :: ShowF r => (forall tp . Doc ann -> p tp -> Doc ann) -> LocMap r p -> [Doc ann]
ppLocMap f m =
  let ppPair (Pair l v) = f (pretty l) v
   in ppPair <$> locMapToList m

-- | Return value associated with location or nothing if it is not
-- defined.
locLookup :: (MemWidth (RegAddrWidth r), OrdF r)
          => BoundLoc r tp
          -> LocMap r v
          -> Maybe (v tp)
locLookup (RegLoc r) m = MapF.lookup r (locMapRegs m)
locLookup (StackOffLoc o repr) m =
  case memMapLookup o repr (locMapStack m) of
    MMLResult r -> Just r
    MMLOverlap _ _ _ -> Nothing
    MMLNone -> Nothing

-- | This associates the location with a value in the map, replacing any existing binding.
--
-- It is prefixed with "nonOverlap" because it doesn't guarantee that stack
-- values are non-overlapping -- the user should ensure this before calling this.
nonOverlapLocInsert :: OrdF r => BoundLoc r tp -> v tp -> LocMap r v -> LocMap r v
nonOverlapLocInsert (RegLoc r) v m =
  m { locMapRegs = MapF.insert r v (locMapRegs m) }
nonOverlapLocInsert (StackOffLoc off repr) v m =
  m { locMapStack = unsafeMemMapInsert off repr v (locMapStack m) }

locOverwriteWith :: (OrdF r, MemWidth (RegAddrWidth r))
                 => (v tp -> v tp -> v tp) -- ^ Update takes new and  old.
                 -> BoundLoc r tp
                 -> v tp
                 -> LocMap r v
                 -> LocMap r v
locOverwriteWith upd (RegLoc r) v m =
  m { locMapRegs = MapF.insertWith upd r v (locMapRegs m) }
locOverwriteWith upd (StackOffLoc o repr) v m =
  let nv = case memMapLookup o repr (locMapStack m) of
             MMLNone -> v
             MMLOverlap _ _ _ -> v
             MMLResult oldv -> upd v oldv
   in m { locMapStack = memMapOverwrite o repr nv (locMapStack m) }

------------------------------------------------------------------------
-- StackEqConstraint

-- | A constraint on the value stored in a location (i.e., register or
-- stack offset) at the start of block executino.
data StackEqConstraint r tp where
  -- | This indicates the value is equal to the frame pointer plus the
  -- given offset.
  --
  -- As stacks grow down on many architectures, the offset will
  -- typically be negative.
  IsStackOff :: !(MemInt (RegAddrWidth r)) -> StackEqConstraint r (BVType (RegAddrWidth r))
  -- | Indicates the value is equal to the value stored at the
  -- location.
  EqualLoc   :: !(BoundLoc r tp) -> StackEqConstraint r tp
  -- | Indicates the value is the unsigned extension of the value
  -- at another location.
  IsUExt :: (1 <= u, u+1 <= w)
         => !(BoundLoc r (BVType u))
         -> !(NatRepr w)
         -> StackEqConstraint r (BVType w)


ppStackEqConstraint :: ShowF r => Doc ann -> StackEqConstraint r tp -> Doc ann
ppStackEqConstraint d (IsStackOff i) =
  d <+> "= stack_frame" <+> ppAddend i
ppStackEqConstraint d (EqualLoc   l) = d <> " = " <> pretty l
ppStackEqConstraint d (IsUExt l w) = d <> " = (uext " <> pretty l <+> viaShow w <> ")"

------------------------------------------------------------------------
-- BlockStartStackConstraints

-- | Constraints on start of block.
--
-- This datatype maintains equality constraints between locations and
-- stack offsets.  It is used in jump bounds and other analysis
-- libraries where we want to know when two registers or stack
-- locations are equal.
newtype BlockStartStackConstraints arch =
  BSSC { unBSSC :: LocMap (ArchReg arch) (StackEqConstraint (ArchReg arch)) }

-- | Pretty print the lines in stack constraints.
ppBlockStartStackConstraints :: ShowF (ArchReg arch)
                             => BlockStartStackConstraints arch
                             -> [Doc ann]
ppBlockStartStackConstraints = ppLocMap ppStackEqConstraint . unBSSC

fnEntryBlockStartStackConstraints :: RegisterInfo (ArchReg arch)
                                  => BlockStartStackConstraints arch
fnEntryBlockStartStackConstraints =
  BSSC { unBSSC =
           LocMap { locMapRegs = MapF.singleton sp_reg (IsStackOff 0)
                  , locMapStack = emptyMemMap
                  }
       }

-- | @blockStartLocStackOffset c l@ determines if @l@ has the form @stack_frame + o@
-- using the constraints @c@ for some stack offset @o@.
--
-- If it does, then this returns @Just o@.  Otherwise it returns @Nothing@.
blockStartLocStackOffset :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                         => BlockStartStackConstraints arch
                         -> BoundLoc (ArchReg arch) tp
                         -> Maybe (MemInt (ArchAddrWidth arch))
blockStartLocStackOffset cns loc =
  case locLookup loc (unBSSC cns) of
    Nothing -> Nothing
    Just (IsStackOff o) -> Just o
    Just (EqualLoc loc') -> blockStartLocStackOffset cns loc'
    -- Unsigned extensions cannot be stack offsets.
    Just (IsUExt _ _) -> Nothing

-- | Constraint on a class representative
data StackOffConstraint r tp where
  StackOffCns :: !(MemInt (RegAddrWidth r)) -> StackOffConstraint r (BVType (RegAddrWidth r))
  UExtCns :: (1 <= u, u+1 <= w)
          => !(BoundLoc r (BVType u))
          -> !(NatRepr w)
          -> StackOffConstraint r (BVType w)

instance TestEquality r => Eq (StackOffConstraint r tp) where
  StackOffCns i == StackOffCns j = i == j
  UExtCns xl _ == UExtCns yl _ =
    case testEquality xl yl of
      Just Refl -> True
      Nothing  -> False
  _ == _ = False

-- | @boundsLocRep cns loc@ returns the representative location for
-- @loc@.
--
-- This representative location has the property that a location must
-- have the same value as its representative location, and if two
-- locations have provably equal values in @cns@, then they must
-- have the same representative.
blockStartLocRepAndCns :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                       => BlockStartStackConstraints arch
                       -> BoundLoc (ArchReg arch) tp
                       -> ( BoundLoc (ArchReg arch) tp
                          , Maybe (StackOffConstraint (ArchReg arch) tp)
                          )
blockStartLocRepAndCns cns l =
  case locLookup l (unBSSC cns) of
    Just (EqualLoc loc) -> blockStartLocRepAndCns cns loc
    Just (IsStackOff o) -> (l, Just (StackOffCns o))
    Just (IsUExt loc w) -> (l, Just (UExtCns loc w))
    Nothing -> (l, Nothing)

------------------------------------------------------------------------
-- joinStackExpr

-- | Maps representatives from old and new join constraints to
-- representative in merged map.
type JoinClassMap r = MapF (JoinClassPair (BoundLoc r)) (BoundLoc r)

-- | Information needed to join classes.
data JoinContext s arch = JoinContext { jctxOldCns :: !(BlockStartStackConstraints arch)
                                        -- ^ Old constraints being joined
                                      , jctxNewCns :: !(BlockStartStackConstraints arch)
                                        -- ^ New constraints being joined.
                                      , jctxNextCnsRef :: !(STRef s (BlockStartStackConstraints arch))
                                        -- ^ Reference maintaining current bounds.
                                      , jctxClassMapRef :: !(STRef s (JoinClassMap (ArchReg arch)))
                                        -- ^ The map from (oldClassRep, newClassRep) pairs to the
                                        -- next class map.
                                      , jctxClassCountRef :: !(STRef s Int)
                                        -- ^ Reference that stores numbers of classes seen in
                                        -- old reference so we can see if new number of classes
                                        -- is different.
                                      }

-- | @setNextConstraint ctx loc cns@ asserts that @loc@ satisfies the
-- constraint @cns@ in the next constraint ref of @ctx@.
setNextConstraint :: OrdF (ArchReg arch)
                  => JoinContext s arch
                  -> BoundLoc (ArchReg arch) tp
                  -> StackEqConstraint (ArchReg arch) tp
                  -> Changed s ()
setNextConstraint ctx thisLoc eqCns =
  changedST $  modifySTRef' (jctxNextCnsRef ctx) $ \cns ->
    BSSC (nonOverlapLocInsert thisLoc eqCns (unBSSC cns))

type LocConPair r tp = (BoundLoc r tp, Maybe (StackOffConstraint r tp))

-- | @locAreEqual cns x y@ return true if @cns |= x = y@.
locAreEqual :: ( MemWidth (ArchAddrWidth arch)
               , OrdF (ArchReg arch)
               )
            => BlockStartStackConstraints arch
            -> BoundLoc (ArchReg arch) tp
            -> BoundLoc (ArchReg arch) tp
            -> Bool
locAreEqual cns x y =
  let (xr, _) = blockStartLocRepAndCns cns x
      (yr, _) = blockStartLocRepAndCns cns y
   in xr == yr

joinNextLoc :: forall s arch tp
           .  ( MemWidth (ArchAddrWidth arch)
              , OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              )
           => JoinContext s arch
           -> BoundLoc (ArchReg arch) tp
              -- ^ Location to use for next representative if we need
              -- need to make old.
           -> LocConPair (ArchReg arch) tp
           -> Changed s (BoundLoc (ArchReg arch) tp)
joinNextLoc ctx thisLoc (oldRep, oldPred) = do
  -- Get representative in new lcoaton.
  let (newRep, newPred) = blockStartLocRepAndCns (jctxNewCns ctx) thisLoc
  m <- changedST $ readSTRef (jctxClassMapRef ctx)
  -- Make pair containing old and new rep so we can lookup if we
  -- already have visited this class.
  let pair = JoinClassPair oldRep newRep
  case MapF.lookup pair m of
    -- If we have visited then we just assert @thisLoc@ is equal to
    -- the previously added rep.
    Just resRep -> do
      -- Assert r is equal to resRep
      setNextConstraint ctx thisLoc (EqualLoc resRep)
      return resRep
    -- If we have not visited these reps, then we need to join the
    -- constraint
    Nothing -> do
      changedST $ writeSTRef (jctxClassMapRef ctx) $! MapF.insert pair thisLoc m
      case (oldPred, newPred) of
        (Nothing, _) ->
          pure ()
        (Just (StackOffCns x), Just (StackOffCns y))
          | x == y -> do
            setNextConstraint ctx thisLoc (IsStackOff x)
          -- In old, thisLoc == uext xl w
          -- In new, thisLoc == uext yl w
          -- We see if xl and yl have same rep in old loc.
          -- If so, then we
        (Just (UExtCns xl w), Just (UExtCns yl _))
          | Just Refl <- testEquality (typeWidth xl) (typeWidth yl)
          , locAreEqual (jctxOldCns ctx) xl yl
          , locAreEqual (jctxNewCns ctx) xl yl -> do
            let xlRep = blockStartLocRepAndCns (jctxOldCns ctx) xl
            nextSubRep <- joinNextLoc ctx xl xlRep
            setNextConstraint ctx thisLoc (IsUExt nextSubRep w)
        (Just _, _) -> do
          markChanged True
      pure thisLoc

-- | @joinOldLoc ctx l eq@ visits a location in a old map and ensures
-- it is bound.
joinOldLoc :: forall s arch tp
           .  ( MemWidth (ArchAddrWidth arch)
              , OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              )
           => JoinContext s arch
           -> BoundLoc (ArchReg arch) tp
              -- ^ Location that appears in old constraints.
           -> StackEqConstraint (ArchReg arch) tp
              -- ^ Constraint on location in original list.
           -> Changed s ()
joinOldLoc ctx thisLoc oldCns = do
  oldRepPredPair <- changedST $
    case oldCns of
      EqualLoc oldLoc ->
        pure (blockStartLocRepAndCns (jctxOldCns ctx) oldLoc)
      IsStackOff o -> do
        -- Increment number of equivalence classes when we see an old
        -- representative.
        modifySTRef' (jctxClassCountRef ctx) (+1)
        -- Return this loc
        pure (thisLoc, Just (StackOffCns o))
      IsUExt oldSubLoc w -> do
        -- Increment number of equivalence classes when we see an old
        -- representative.
        modifySTRef' (jctxClassCountRef ctx) (+1)
        let (subRep, _) = blockStartLocRepAndCns (jctxOldCns ctx) oldSubLoc
        pure (thisLoc, Just (UExtCns subRep w))
  _ <- joinNextLoc ctx thisLoc oldRepPredPair
  pure ()

-- | Return a jump bounds that implies both input bounds, or `Nothing`
-- if every fact inx the old bounds is implied by the new bounds.
joinBlockStartStackConstraints
  :: forall arch s
  .  (MemWidth (ArchAddrWidth arch)
     , OrdF (ArchReg arch)
     , HasRepr (ArchReg arch) TypeRepr
     )
  => BlockStartStackConstraints arch
  -> BlockStartStackConstraints arch
  -> Changed s (BlockStartStackConstraints arch, JoinClassMap (ArchReg arch))
joinBlockStartStackConstraints old new = do
  -- Reference to new bounds.
  cnsRef <- changedST $ newSTRef (BSSC locMapEmpty)
  -- This maps pairs containing the class representative in the old
  -- and new maps to the associated class representative in the
  -- combined bounds.
  procRef <- changedST $ newSTRef MapF.empty
  cntr    <- changedST $ newSTRef 0
  let ctx = JoinContext { jctxOldCns = old
                        , jctxNewCns = new
                        , jctxNextCnsRef = cnsRef
                        , jctxClassMapRef = procRef
                        , jctxClassCountRef = cntr
                        }
  locMapTraverseWithKey_ (joinOldLoc ctx) (unBSSC old)
  -- Check number of equivalence classes in result and original
  -- The count should not have decreased, but may increase if two elements
  -- are no longer equal, and we need to check this.
  origClassCount   <- changedST $ readSTRef cntr
  resultClassCount <- changedST $ MapF.size <$> readSTRef procRef
  unless (origClassCount <= resultClassCount) $ do
    error "Original class count should be bound by resultClassCount"
  -- Record changed if any classes are different.
  markChanged (origClassCount < resultClassCount)
  changedST $ (,) <$> readSTRef cnsRef <*> readSTRef procRef

------------------------------------------------------------------------
-- StackExpr

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
data StackExpr arch ids tp where
  -- | This refers to the value that a location had at the start of
  -- block execution.
  --
  -- The location should be a class representative in the initial bounds.
  ClassRepExpr :: !(BoundLoc (ArchReg arch) tp) -> StackExpr arch ids tp
  -- | An assignment that is not interpreted, and just treated as a constant.
  UninterpAssignExpr :: !(AssignId ids tp)
                     -> !(AssignRhs arch (Value arch ids) tp)
                     -> StackExpr arch ids tp
  -- | Denotes the value of the stack pointer at function start plus some constant.
  StackOffsetExpr :: !(MemInt (ArchAddrWidth arch))
                  -> StackExpr arch ids (BVType (ArchAddrWidth arch))
  -- | Denotes a constant
  CExpr :: !(CValue arch tp) -> StackExpr arch ids tp

  -- | This is a pure function applied to other index expressions that
  -- may be worth interpreting (but could be treated as an uninterp
  -- assign expr also.
  UExtExpr :: (1 <= u, u+1 <= w)
           => StackExpr arch ids (BVType u)
           -> NatRepr w
           -> StackExpr arch ids (BVType w)

  -- | This is a pure function applied to other index expressions that
  -- may be worth interpreting (but could be treated as an uninterp
  -- assign expr also.
  AppExpr :: !(AssignId ids tp)
          -> !(App (StackExpr arch ids) tp)
          -> StackExpr arch ids tp

instance ShowF (ArchReg arch) => Show (StackExpr arch ids tp) where
  show (ClassRepExpr l) = "(ClassRepExpr " <> show l <> ")"
  show (UninterpAssignExpr a _r) = "(UninterpAssignExpr " <> show a <> " _)"
  show (StackOffsetExpr o) = "(StackOffsetExpr " <> show o <> ")"
  show (CExpr c) = "(CExpr " <> show c <> ")"
  show (UExtExpr u w) = "(UExtExpr " <> show u <> " " <> show w <> ")"
  show (AppExpr a _r) = "(AppExpr " <> show a <> " _)"

instance TestEquality (ArchReg arch) => TestEquality (StackExpr arch ids) where
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
  testEquality (UExtExpr x xw) (UExtExpr y yw) = do
    Refl <- testEquality xw yw
    Refl <- testEquality x y
    pure Refl
  testEquality (AppExpr xn _xa) (AppExpr yn _ya) =
    testEquality xn yn
  testEquality _ _ = Nothing

instance OrdF (ArchReg arch) => OrdF (StackExpr arch ids) where
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

  compareF (UExtExpr x xw) (UExtExpr y yw) =
    joinOrderingF (compareF xw yw) $
    joinOrderingF (compareF x y) $ EQF
  compareF UExtExpr{} _ = LTF
  compareF _ UExtExpr{} = GTF

  compareF (AppExpr xn _xa) (AppExpr yn _ya) = compareF xn yn

instance TestEquality (ArchReg arch) => Eq (StackExpr arch ids tp) where
  x == y = isJust (testEquality x y)

instance OrdF (ArchReg arch) => Ord (StackExpr arch ids tp) where
  compare x y = toOrdering (compareF x y)

instance ( HasRepr (ArchReg arch) TypeRepr
         , MemWidth (ArchAddrWidth arch)
         ) => HasRepr (StackExpr arch ids) TypeRepr where
  typeRepr e =
    case e of
      ClassRepExpr x    -> typeRepr x
      UninterpAssignExpr _ rhs   -> typeRepr rhs
      StackOffsetExpr _ -> addrTypeRepr
      CExpr x           -> typeRepr x
      UExtExpr (_ :: StackExpr arch ids (BVType u)) (w :: NatRepr w) ->
        case leqTrans (leqAdd (LeqProof @1 @u) (Proxy :: Proxy 1)) (LeqProof @(u+1) @w) of
          LeqProof -> BVTypeRepr w
      AppExpr _ a       -> typeRepr a

instance ShowF (ArchReg arch) => Pretty (StackExpr arch id tp) where
  pretty e =
    case e of
      ClassRepExpr l -> pretty l
      UninterpAssignExpr n _ -> parens ("uninterp" <+> ppAssignId n)
      StackOffsetExpr o
        | memIntValue o > 0 -> parens ("+ stack_off" <+> pretty o)
        | memIntValue o < 0 -> parens ("- stack_off" <+> pretty (negate (toInteger (memIntValue o))))
        | otherwise -> "stack_off"
      CExpr v -> pretty v
      UExtExpr l w -> parens ("uext " <> pretty l <+> viaShow w)
      AppExpr n _ -> ppAssignId n

instance ShowF (ArchReg arch) => PrettyF (StackExpr arch id) where
  prettyF = pretty

-- | Return an expression equivalent to the location in the constraint
-- map.
--
-- This attempts to normalize the expression to get a representative.
blockStartLocExpr :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => BlockStartStackConstraints arch
                  -> BoundLoc (ArchReg arch) tp
                  -> StackExpr arch ids tp
blockStartLocExpr cns loc =
  case locLookup loc (unBSSC cns) of
    Nothing -> ClassRepExpr loc
    Just (IsStackOff o) -> StackOffsetExpr o
    Just (EqualLoc loc') -> blockStartLocExpr cns loc'
    Just (IsUExt loc' w) -> UExtExpr (blockStartLocExpr cns loc') w

------------------------------------------------------------------------
-- BlockIntraStackConstraints

-- | Information about bounds for a particular value within a block.
data BlockIntraStackConstraints arch ids
   = BISC { biscInitConstraints :: !(BlockStartStackConstraints arch)
            -- ^ Bounds at execution start.
          , stackExprMap :: !(MemMap (MemInt (ArchAddrWidth arch)) (StackExpr arch ids))
            -- ^ Maps stack offsets to the expression associated with them at the current
            -- location.
          , assignExprMap :: !(MapF (AssignId ids) (StackExpr arch ids))
            -- ^ Maps processed assignments to index expressions.
          }

instance ShowF (ArchReg arch) => Pretty (BlockIntraStackConstraints arch ids) where
  pretty cns =
    let ppStk :: MemInt (ArchAddrWidth arch) -> MemRepr tp -> StackExpr arch ids tp -> Doc ann
        ppStk o r v = viaShow o <> ", " <> pretty r <> " := " <> pretty v
        sm :: Doc ann
        sm = memMapFoldrWithKey (\o r v d -> vcat [ppStk o r v, d]) emptyDoc (stackExprMap cns)
        ppAssign :: AssignId ids tp -> StackExpr arch ids tp -> Doc ann -> Doc ann
        ppAssign a (AppExpr u app) d =
          case testEquality a u of
            Nothing -> vcat [ppAssignId a <> " := " <> ppAssignId u, d]
            Just Refl -> vcat [ppAssignId a <> " := " <> ppApp pretty app, d]
        ppAssign a e d = vcat [ppAssignId a <> " := " <> pretty e, d]
        am :: Doc ann
        am = MapF.foldrWithKey ppAssign emptyDoc (assignExprMap cns)
     in vcat [ "stackExprMap:"
             , indent 2 sm
             , "assignExprMap:"
             , indent 2 am
             ]


-- | Create index bounds from initial index bounds.
mkBlockIntraStackConstraints :: forall arch ids
                             .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                             => BlockStartStackConstraints arch
                             -> BlockIntraStackConstraints arch ids
mkBlockIntraStackConstraints cns =
  let stackExpr :: MemInt (ArchAddrWidth arch)
                -> MemRepr tp
                -> StackEqConstraint (ArchReg arch) tp
                -> StackExpr arch ids tp
      stackExpr i tp _ = blockStartLocExpr cns (StackOffLoc i tp)
   in BISC { biscInitConstraints = cns
           , stackExprMap   = memMapMapWithKey stackExpr (locMapStack (unBSSC cns))
           , assignExprMap  = MapF.empty
           }

-- | Return the value of the index expression given the bounds.
intraStackValueExpr :: forall arch ids tp
                    .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                    => BlockIntraStackConstraints arch ids
                    -> Value arch ids tp
                    -> StackExpr arch ids tp
intraStackValueExpr cns val =
  case val of
    CValue c -> CExpr c
    AssignedValue (Assignment aid _) ->
      case MapF.lookup aid (assignExprMap cns) of
        Just e -> e
        Nothing ->
          error $ printf "Expected %s to be assigned." (show (ppAssignId aid))
    Initial r -> blockStartLocExpr (biscInitConstraints cns) (RegLoc r)

-- | Return an expression associated with the @AssignRhs@.
intraStackRhsExpr :: forall arch ids tp
                  .  ( MemWidth (ArchAddrWidth arch)
                     , OrdF (ArchReg arch)
                     , ShowF (ArchReg arch)
                     )
                  => BlockIntraStackConstraints arch ids
                  -> AssignId ids tp
                  -> AssignRhs arch (Value arch ids) tp
                  -> StackExpr arch ids tp
intraStackRhsExpr cns aid arhs =
  case arhs of
    EvalApp (UExt x w) ->
      UExtExpr (intraStackValueExpr cns x) w
    EvalApp app -> do
      let stackFn v =
            case intraStackValueExpr cns v of
              StackOffsetExpr i -> Just (toInteger i)
              _ -> Nothing
      case appAsStackOffset stackFn app of
        Just (StackOffsetView o) -> do
          StackOffsetExpr $ fromInteger o
        _ ->
          let a = fmapFC (intraStackValueExpr cns) app
           in AppExpr aid a
    ReadMem addr repr
      | StackOffsetExpr o <- intraStackValueExpr cns addr
      , MMLResult e <- memMapLookup o repr (stackExprMap cns) ->
        e
    _ -> UninterpAssignExpr aid arhs

-- | Associate the given bound expression with the assignment.
intraStackSetAssignId :: AssignId ids tp
                      -> StackExpr arch ids tp
                      -> BlockIntraStackConstraints arch ids
                      -> BlockIntraStackConstraints arch ids
intraStackSetAssignId aid expr cns =
  cns { assignExprMap = MapF.insert aid expr (assignExprMap cns) }

-- | Discard information about memory due to an operation that may
-- affect arbitrary memory.
discardMemInfo :: BlockIntraStackConstraints arch ids
               -> BlockIntraStackConstraints arch ids
discardMemInfo cns =
  cns { stackExprMap = emptyMemMap }

-- | Update the stack to point to the given expression.
writeStackOff :: forall arch ids tp
              .  (MemWidth (ArchAddrWidth arch), OrdF  (ArchReg arch))
              => BlockIntraStackConstraints arch ids
              -> MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> Value arch ids tp
              -> BlockIntraStackConstraints arch ids
writeStackOff cns off repr v =
  cns { stackExprMap = memMapOverwrite off repr (intraStackValueExpr cns v) (stackExprMap cns) }

------------------------------------------------------------------------
-- NextStateMonad

-- | Maps bound expression that have been visited to their location.
--
-- We memoize expressions seen so that we can infer when two locations
-- must be equal.
data NextBlockState arch ids =
  NBS { nbsExprMap :: !(MapF (StackExpr arch ids) (BoundLoc (ArchReg arch) ))
      , nbsRepLocs :: ![Pair (BoundLoc (ArchReg arch)) (StackExpr arch ids)]
        -- ^ List of location expression pairs
      }

-- Monad used for computing next states.
newtype NextStateMonad arch ids a = NSM (State (NextBlockState arch ids) a)
  deriving (Functor, Applicative, Monad)

runNextStateMonad :: NextStateMonad arch ids a -> a
runNextStateMonad (NSM m) = evalState m $! NBS { nbsExprMap = MapF.empty, nbsRepLocs = [] }

-- | Return a list of locations and associated expressions that
-- represent equivalence classes in the next state.
--
-- Note that each equivalence class has a unique stack expression, so
-- all the locations in an equivalence class should have the same
-- expression.
getNextStateRepresentatives
  :: NextStateMonad arch ids [Pair (BoundLoc (ArchReg arch)) (StackExpr arch ids)]
getNextStateRepresentatives = NSM $ gets nbsRepLocs

------------------------------------------------------------------------
-- BlockIntraStackConstraints next state

-- | Return the constraint associated with the given location and expression
-- or nothing if the constraint is the top one and should be stored.
nextStateStackEqConstraint
  :: ( MemWidth (ArchAddrWidth arch)
     , HasRepr (ArchReg arch) TypeRepr
     , OrdF (ArchReg arch)
     , ShowF (ArchReg arch)
     )
  => BoundLoc (ArchReg arch) tp
     -- ^ Location expression is stored at.
  -> StackExpr arch ids tp
     -- ^ Expression to infer predicate for.
  -> NextStateMonad arch ids (Maybe (StackEqConstraint (ArchReg arch) tp))
nextStateStackEqConstraint loc e = do
  s <- NSM $ get
  case MapF.lookup e (nbsExprMap s) of
    Just l ->
      pure $! Just $ EqualLoc l
    Nothing -> do
      NSM $ put $! NBS { nbsExprMap = MapF.insert e loc (nbsExprMap s)
                       , nbsRepLocs = Pair loc e : nbsRepLocs s
                       }
      case e of
        StackOffsetExpr o ->
          pure $! (Just $! IsStackOff o)
        _ ->
          pure $! Nothing

-- | Bounds for block after jump
postJumpStackConstraints :: forall arch ids
                         .  RegisterInfo (ArchReg arch)
                         => BlockIntraStackConstraints arch ids
                         -- ^ Constraints at end of block.
                         -> RegState (ArchReg arch) (Value arch ids)
                         -- ^ Register values at start of next state.
                         --
                         -- Note. ip_reg is ignored, so it does not have to be up-to-date.
                         -> NextStateMonad arch ids (BlockStartStackConstraints arch)
postJumpStackConstraints cns regs = do
  let postReg :: ArchReg arch tp
              -> Value arch ids tp
              -> NextStateMonad arch ids (Maybe (StackEqConstraint (ArchReg arch) tp))
      postReg r v =
        case testEquality r ip_reg of
          Just Refl -> pure Nothing
          Nothing -> nextStateStackEqConstraint (RegLoc r) (intraStackValueExpr cns v)
  rm <- MapF.traverseMaybeWithKey postReg (regStateMap regs)
  sm <- memMapTraverseMaybeWithKey
          (\i repr e -> nextStateStackEqConstraint (StackOffLoc i repr) e)
          (stackExprMap cns)
  pure $! BSSC (LocMap { locMapRegs = rm, locMapStack = sm })

-- | Get the constraint associated with a register after a call.
postCallConstraint :: RegisterInfo (ArchReg arch)
                   => CallParams (ArchReg arch)
                      -- ^ Information about calling convention.
                   -> BlockIntraStackConstraints arch ids
                      -- ^ Bounds at end of this state.
                   -> ArchReg arch tp
                   -- ^ Register to get
                   -> Value arch ids tp
                   -- ^ Value of register at time call occurs.
                   -> NextStateMonad arch ids (Maybe (StackEqConstraint (ArchReg arch) tp))
postCallConstraint params cns r v
  | Just Refl <- testEquality r ip_reg =
      pure Nothing
  | Just Refl <- testEquality r sp_reg
  , StackOffsetExpr o <- intraStackValueExpr cns v = do
      pure $! (Just $! IsStackOff (o+fromInteger (postCallStackDelta params)))
  | preserveReg params r =
      nextStateStackEqConstraint (RegLoc r) (intraStackValueExpr cns v)
  | otherwise =
      pure Nothing

-- | Return the index bounds after a function call.
postCallStackConstraints :: forall arch ids
                         .  RegisterInfo (ArchReg arch)
                         => CallParams (ArchReg arch)
                         -> BlockIntraStackConstraints arch ids
                         -> RegState (ArchReg arch) (Value arch ids)
                         -> NextStateMonad arch ids (BlockStartStackConstraints arch)
postCallStackConstraints params cns regs = do
  rm <- MapF.traverseMaybeWithKey (postCallConstraint params cns) (regStateMap regs)

  let finalStack = stackExprMap cns
  let filteredStack =
        case intraStackValueExpr cns (getBoundValue sp_reg regs) of
          StackOffsetExpr spOff
            | stackGrowsDown params ->
                let newOff = toInteger spOff + postCallStackDelta params
                    -- Keep entries at offsets above return address.
                 in memMapDropBelow newOff finalStack
            | otherwise ->
                let newOff = toInteger spOff + postCallStackDelta params
                    -- Keep entries whose high address is below new stack offset
                 in memMapDropAbove newOff finalStack
          _ -> emptyMemMap
  let nextStackFn :: MemInt (ArchAddrWidth arch)
                  -> MemRepr tp
                  -> StackExpr arch ids tp
                  -> NextStateMonad arch ids (Maybe (StackEqConstraint (ArchReg arch) tp))
      nextStackFn i repr e =
        nextStateStackEqConstraint (StackOffLoc i repr) e
  sm <- memMapTraverseMaybeWithKey nextStackFn filteredStack
  pure $! BSSC (LocMap { locMapRegs = rm
                       , locMapStack = sm
                       })
