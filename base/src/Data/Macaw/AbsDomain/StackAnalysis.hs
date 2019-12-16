{- |

This module defines a relational abstract domain for tracking
registers and stack addresses.  The model records when one of these
values is known to be equal to the current pointer stack frame.  This
domain also tracks equalities between nodes so that analysis
algorithms built on top of this are modulo known equivalences
between registers and stack locations.

-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
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
  , StackOffConstraint
  , blockStartLocRepAndCns
  , BoundLoc(..)
  , joinBlockStartStackConstraints
  , JoinClassMap
  , JoinClassPair(..)
    -- ** BlockIntraStackConstraints
  , BlockIntraStackConstraints
  , mkBlockIntraStackConstraints
  , biscInitConstraints
  , blockIntraValueExpr
  , blockIntraValueStackOffset
  , StackExpr(..)
  , blockIntraRhsExpr
  , bindAssignment
  , discardStackInfo
  , writeStackOff
    -- ** Block terminator updates
  , postJumpStackConstraints
  , postCallStackConstraints
    -- * LocMap
  , LocMap(..)
  , locMapEmpty
  , locLookup
  , nonOverlapLocInsert
  , locOverwriteWith
  , ppLocMap
    -- * StackMap
  , StackMap
  , emptyStackMap
  , stackMapLookup
  , StackMapLookup(..)
  , stackMapOverwrite
  , stackMapMapWithKey
  , stackMapTraverseMaybeWithKey
  , stackMapDropAbove
  , stackMapDropBelow
    -- * NextStateMonad
  , NextStateMonad
  , runNextStateMonad
  , getNextStateRepresentatives
    -- * Miscelaneous
  ) where

import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Functor
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Pair
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           Data.STRef
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.AbsDomain.CallParams
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import qualified Data.Macaw.Types as M
import           Data.Macaw.Types hiding (Type)
import           Data.Macaw.Utils.Changed

addrTypeRepr :: MemWidth w => TypeRepr (BVType w)
addrTypeRepr = BVTypeRepr memWidthNatRepr

ppAddend :: MemInt w -> Doc
ppAddend o | memIntValue o < 0 =
               text "-" <+> pretty (negate (toInteger (memIntValue o)))
           | otherwise = text "+" <+> pretty o

ppStackOff :: MemInt w -> MemRepr tp -> Doc
ppStackOff o repr =
  text "*(stack_frame" <+> ppAddend o <> text "," <+> pretty repr <> text ")"

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
        -- If previous write ends after this write starts
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

-- | Pretty print a location map.
ppLocMap :: ShowF r => (forall tp . Doc -> p tp -> Doc) -> LocMap r p -> [Doc]
ppLocMap f m
  = flip (MapF.foldrWithKey (\k v -> (f (text (showF k)) v:)))
                            (locMapRegs m)
  $ stackMapFoldrWithKey (\i repr v -> (f (ppStackOff i repr) v:))
                         []
                         (locMapStack m)

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
-- StackEqConstraint

-- | A constraint on a location for the stack analysis.
data StackEqConstraint r tp where
  -- | An equivalence class representative with the given number of
  -- elements.
  --
  -- In our map the number of equivalence class members should always
  -- be positive.
  IsStackOff :: !(MemInt (RegAddrWidth r)) -> StackEqConstraint r (BVType (RegAddrWidth r))
  EqualLoc   :: !(BoundLoc r tp) -> StackEqConstraint r tp

ppStackEqConstraint :: ShowF r => Doc -> StackEqConstraint r tp -> Doc
ppStackEqConstraint d (IsStackOff i) =
  d <+> text "= stack_frame" <+> ppAddend i
ppStackEqConstraint d (EqualLoc   l) = d <+> text "=" <+> pretty l

------------------------------------------------------------------------
-- BlockStartStackConstraints

-- | Constraints on start of block
newtype BlockStartStackConstraints arch =
  BSSC { unBSSC :: LocMap (ArchReg arch) (StackEqConstraint (ArchReg arch)) }

-- | Pretty print the lines in stack constraints.
ppBlockStartStackConstraints :: ShowF (ArchReg arch) => BlockStartStackConstraints arch -> [Doc]
ppBlockStartStackConstraints = ppLocMap ppStackEqConstraint . unBSSC

fnEntryBlockStartStackConstraints :: RegisterInfo (ArchReg arch) => BlockStartStackConstraints arch
fnEntryBlockStartStackConstraints =
  BSSC  LocMap { locMapRegs = MapF.singleton sp_reg (IsStackOff 0)
               , locMapStack = emptyStackMap
               }

-- | @blockStartLocStackOffset c l@ returns an offset of the stack
-- pointer that the value stored in @l@ is inferred to be equivalent
-- to when the block starts execution.
blockStartLocStackOffset :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                         => BlockStartStackConstraints arch
                         -> BoundLoc (ArchReg arch) tp
                         -> Maybe (MemInt (ArchAddrWidth arch))
blockStartLocStackOffset cns loc =
  case locLookup loc (unBSSC cns) of
    Nothing -> Nothing
    Just (IsStackOff o) -> Just o
    Just (EqualLoc loc') -> blockStartLocStackOffset cns loc'

data StackOffConstraint w tp where
  StackOffCns :: !(MemInt w) -> StackOffConstraint w (BVType w)

-- | @boundsLocRep bnds loc@ returns the representative location for
-- @loc@.
--
-- This representative location has the property that a location must
-- have the same value as its representative location, and if two
-- locations have provably equal values in the bounds, then they must
-- have the same representative.
blockStartLocRepAndCns :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                       => BlockStartStackConstraints arch
                       -> BoundLoc (ArchReg arch) tp
                       -> (BoundLoc (ArchReg arch) tp, Maybe (StackOffConstraint (ArchAddrWidth arch) tp))
blockStartLocRepAndCns cns l =
  case locLookup l (unBSSC cns) of
    Just (EqualLoc loc) -> blockStartLocRepAndCns cns loc
    Just (IsStackOff o) -> (l,Just (StackOffCns o))
    Nothing -> (l, Nothing)

------------------------------------------------------------------------
-- joinStackExpr

type JoinClassMap r = MapF (JoinClassPair (BoundLoc r)) (BoundLoc r)

joinStackEqConstraint :: Maybe (StackOffConstraint w tp)
                      -> Maybe (StackOffConstraint w tp)
                      -> Changed s (Maybe (StackOffConstraint w tp))
joinStackEqConstraint Nothing _ = pure Nothing
joinStackEqConstraint p@(Just (StackOffCns i)) (Just (StackOffCns j)) | i == j = pure p
joinStackEqConstraint _ _ = markChanged True $> Nothing

-- | Join locations
joinNewLoc :: forall s arch tp
           .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
           => BlockStartStackConstraints arch
           -> BlockStartStackConstraints arch
           -> STRef s (BlockStartStackConstraints arch)
           -- ^ The current index bounds.
           -> STRef s (JoinClassMap (ArchReg arch))
           -- ^ The map from (oldClassRep, newClassRep) pairs to the
           -- result class rep.
           -> STRef s Int
           -- ^ Stores the number of equivalence classes we have seen in
           -- in the old class
           -- Used so determining if any classes are changed.
           -> BoundLoc (ArchReg arch) tp
              -- ^ Location in join that we have not yet visited.
           -> StackEqConstraint (ArchReg arch) tp
              -- ^ Constraint on location in original list.
           -> Changed s ()
joinNewLoc old new bndsRef procRef cntr thisLoc oldCns = do
  (oldRep, oldPred) <- changedST $
    case oldCns of
      EqualLoc oldLoc ->
        pure (blockStartLocRepAndCns old oldLoc)
      IsStackOff o -> do
        -- Increment number of equivalence classes when we see an old
        -- representative.
        modifySTRef' cntr (+1)
        -- Return this loc
        pure (thisLoc, Just (StackOffCns o))
  let (newRep, newPred) = blockStartLocRepAndCns new thisLoc
  m <- changedST $ readSTRef procRef
  -- See if we have already added a representative for this class.
  let pair = JoinClassPair oldRep newRep
  case MapF.lookup pair m of
    Nothing -> do
      mp <- joinStackEqConstraint oldPred newPred
      changedST $ do
        writeSTRef procRef $! MapF.insert pair thisLoc m
        case mp of
          Nothing -> pure ()
          Just (StackOffCns o) ->
            modifySTRef' bndsRef $ \cns -> BSSC (nonOverlapLocInsert thisLoc (IsStackOff o) (unBSSC cns))
    Just resRep ->
      -- Assert r is equal to resRep
       changedST $
       modifySTRef' bndsRef $ \cns -> BSSC (nonOverlapLocInsert thisLoc (EqualLoc resRep) (unBSSC cns))

-- | Return a jump bounds that implies both input bounds, or `Nothing`
-- if every fact inx the old bounds is implied by the new bounds.
joinBlockStartStackConstraints :: forall arch s
                               .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                               => BlockStartStackConstraints arch
                               -> BlockStartStackConstraints arch
                               -> Changed s (BlockStartStackConstraints arch, JoinClassMap (ArchReg arch))
joinBlockStartStackConstraints old new = do
  -- Reference to new bounds.
  bndsRef <- changedST $ newSTRef (BSSC locMapEmpty)
  -- This maps pairs containing the class representative in the old
  -- and new maps to the associated class representative in the
  -- combined bounds.
  procRef <- changedST $ newSTRef MapF.empty
  cntr    <- changedST $ newSTRef 0
  --
  MapF.traverseWithKey_
    (\r -> joinNewLoc old new bndsRef procRef cntr (RegLoc r))
    (locMapRegs (unBSSC old))
  stackMapTraverseWithKey_
    (\i r c -> joinNewLoc old new bndsRef procRef cntr (StackOffLoc i r) c)
    (locMapStack (unBSSC old))

  -- Check number of equivalence classes in result and original
  -- The count should not have decreased, but may increase if two elements
  -- are no longer equal, and we need to check this.
  origClassCount   <- changedST $ readSTRef cntr
  resultClassCount <- changedST $ MapF.size <$> readSTRef procRef
  unless (origClassCount <= resultClassCount) $ do
    error "Original class count should be bound by resultClassCount"
  -- Record changed if any classes are different.
  markChanged (origClassCount < resultClassCount)

  changedST $ (,) <$> readSTRef bndsRef <*> readSTRef procRef

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
                     -> !(TypeRepr tp)
                     -> StackExpr arch ids tp
  -- | Denotes the value of the stack pointer at function start plus some constant.
  StackOffsetExpr :: !(MemInt (ArchAddrWidth arch))
                  -> StackExpr arch ids (BVType (ArchAddrWidth arch))
  -- | Denotes a constant
  CExpr :: !(CValue arch tp) -> StackExpr arch ids tp

  -- | This is a pure function applied to other index expressions that
  -- may be worth interpreting (but could be treated as an uninterp
  -- assign expr also.
  AppExpr :: !(AssignId ids tp)
          -> !(App (StackExpr arch ids) tp)
          -> StackExpr arch ids tp

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

  compareF (AppExpr xn _xa) (AppExpr yn _ya) = compareF xn yn

instance ( HasRepr (ArchReg arch) TypeRepr
         , MemWidth (ArchAddrWidth arch)
         ) => HasRepr (StackExpr arch ids) TypeRepr where
  typeRepr e =
    case e of
      ClassRepExpr x    -> typeRepr x
      UninterpAssignExpr _ tp   -> tp
      StackOffsetExpr _ -> addrTypeRepr
      CExpr x           -> typeRepr x
      AppExpr _ a       -> typeRepr a

instance ShowF (ArchReg arch) => Pretty (StackExpr arch id tp) where
  pretty e =
    case e of
      ClassRepExpr l -> pretty l
      UninterpAssignExpr n _ -> parens (text "uninterp" <+> ppAssignId n)
      StackOffsetExpr o -> parens (text "+ stack_off" <+> pretty o)
      CExpr v -> pretty v
      AppExpr n _ -> parens (text "app" <+> ppAssignId n)

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
blockStartLocExpr bnds loc =
  case locLookup loc (unBSSC bnds) of
    Nothing -> ClassRepExpr loc
    Just (IsStackOff o) -> StackOffsetExpr o
    Just (EqualLoc loc') -> blockStartLocExpr bnds loc'

------------------------------------------------------------------------
-- BlockIntraStackConstraints

-- | Information about bounds for a particular value within a block.
data BlockIntraStackConstraints arch ids
   = BISC { biscInitConstraints :: !(BlockStartStackConstraints arch)
            -- ^ Bounds at execution start.
          , stackExprMap :: !(StackMap (ArchAddrWidth arch) (StackExpr arch ids))
            -- ^ Maps stack offsets to the expression associated with them.
          , assignExprMap :: !(MapF (AssignId ids) (StackExpr arch ids))
            -- ^ Maps processed assignments to index expressions.
          , memoTable :: !(MapF (App (StackExpr arch ids)) (StackExpr arch ids))
            -- ^ Table for ensuring each bound expression has a single
            -- representative.
          }

-- | Create index bounds from initial index bounds.
mkBlockIntraStackConstraints :: forall arch ids
                             .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                             => BlockStartStackConstraints arch
                             -> BlockIntraStackConstraints arch ids
mkBlockIntraStackConstraints bnds =
  let stackExpr :: MemInt (ArchAddrWidth arch)
                -> MemRepr tp
                -> StackEqConstraint (ArchReg arch) tp
                -> StackExpr arch ids tp
      stackExpr i tp _ = blockStartLocExpr bnds (StackOffLoc i tp)
   in BISC { biscInitConstraints = bnds
           , stackExprMap   = stackMapMapWithKey stackExpr (locMapStack (unBSSC bnds))
           , assignExprMap  = MapF.empty
           , memoTable      = MapF.empty
           }

-- | Return the value of the index expression given the bounds.
blockIntraValueExpr :: forall arch ids tp
                    .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                    => BlockIntraStackConstraints  arch ids
                    -> Value arch ids tp
                    -> StackExpr arch ids tp
blockIntraValueExpr bnds val =
  case val of
    CValue c -> CExpr c
    AssignedValue (Assignment aid _) ->
      case MapF.lookup aid (assignExprMap bnds) of
        Just e -> e
        Nothing -> error $ "blockIntraValueExpr internal: Expected value to be assigned."
    Initial r -> blockStartLocExpr (biscInitConstraints bnds) (RegLoc r)

-- | Return stack offset if value is a stack offset.
blockIntraValueStackOffset :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                           => BlockIntraStackConstraints arch ids
                           -> Value arch ids (BVType (ArchAddrWidth arch))
                           -> Maybe (MemInt (ArchAddrWidth arch))
blockIntraValueStackOffset bnds val =
  case blockIntraValueExpr bnds val of
    StackOffsetExpr i -> Just i
    _ -> Nothing

-- | Return an expression associated with the @AssignRhs@.
blockIntraRhsExpr :: forall arch ids tp
                  .  ( MemWidth (ArchAddrWidth arch)
                     , OrdF (ArchReg arch)
                     , ShowF (ArchReg arch)
                     )
                  => BlockIntraStackConstraints arch ids
                  -> AssignId ids tp
                  -> AssignRhs arch (Value arch ids) tp
                  -> StackExpr arch ids tp
blockIntraRhsExpr bnds aid arhs =
  case arhs of
    EvalApp app -> do
      let stackFn v = toInteger <$> blockIntraValueStackOffset bnds v
      case appAsStackOffset stackFn app of
        Just (StackOffsetView o) -> do
          StackOffsetExpr $ fromInteger o
        _ ->
          let a = fmapFC (blockIntraValueExpr bnds) app
           in case MapF.lookup a (memoTable bnds) of
                Just r -> r
                Nothing -> AppExpr aid a
    ReadMem addr repr
      | Just o <- blockIntraValueStackOffset bnds addr
      , SMLResult e <- stackMapLookup o repr (stackExprMap bnds) ->
        e
    _ -> UninterpAssignExpr aid (typeRepr arhs)

-- | Associate the given bound expression with the assignment.
bindAssignment :: AssignId ids tp
               -> StackExpr arch ids tp
               -> BlockIntraStackConstraints arch ids
               -> BlockIntraStackConstraints arch ids
bindAssignment aid expr bnds =
  bnds { assignExprMap = MapF.insert aid expr (assignExprMap bnds) }

-- | Discard information about the stack in the bounds due to an
-- operation that may affect the stack.
discardStackInfo :: BlockIntraStackConstraints arch ids
                 -> BlockIntraStackConstraints arch ids
discardStackInfo bnds =
  bnds { stackExprMap = emptyStackMap }

-- | Update the stack to point to the given expression.
writeStackOff :: forall arch ids tp
              .  (MemWidth (ArchAddrWidth arch), OrdF  (ArchReg arch))
              => BlockIntraStackConstraints arch ids
              -> MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> Value arch ids tp
              -> BlockIntraStackConstraints arch ids
writeStackOff bnds off repr v =
  bnds { stackExprMap = stackMapOverwrite off repr (blockIntraValueExpr bnds v) (stackExprMap bnds) }

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
getNextStateRepresentatives :: NextStateMonad arch ids [Pair (BoundLoc (ArchReg arch)) (StackExpr arch ids)]
getNextStateRepresentatives = NSM $ gets nbsRepLocs

------------------------------------------------------------------------
-- BlockIntraStackConstraints next state

-- | Return the constraint associated with the given location and expression
-- or nothing if the constraint is the top one and should be stored.
nextStateStackEqConstraint :: ( MemWidth (ArchAddrWidth arch)
                              , HasRepr (ArchReg arch) TypeRepr
                              , OrdF (ArchReg arch)
                              , ShowF (ArchReg arch)
                              )
                           => BoundLoc (ArchReg arch) tp
                           -- ^ Location expression is stored at.
                           -> StackExpr arch ids tp
                           -- ^ Expression to infer predicate or.
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
                         -> NextStateMonad arch ids (BlockStartStackConstraints arch)
postJumpStackConstraints bnds regs = do
  rm <- MapF.traverseMaybeWithKey
          (\r v -> nextStateStackEqConstraint (RegLoc r) (blockIntraValueExpr bnds v))
          (regStateMap regs)
  sm <- stackMapTraverseMaybeWithKey (\i repr e -> nextStateStackEqConstraint (StackOffLoc i repr) e)
                                     (stackExprMap bnds)
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
postCallConstraint params bnds r v
  | Just Refl <- testEquality r sp_reg
  , StackOffsetExpr o <- blockIntraValueExpr bnds v = do
      pure $! (Just $! IsStackOff (o+fromInteger (postCallStackDelta params)))
  | preserveReg params r =
      nextStateStackEqConstraint (RegLoc r) (blockIntraValueExpr bnds v)
  | otherwise =
      pure Nothing

-- | Return the index bounds after a function call.
postCallStackConstraints :: forall arch ids
                            .  RegisterInfo (ArchReg arch)
                         => CallParams (ArchReg arch)
                         -> BlockIntraStackConstraints arch ids
                         -> RegState (ArchReg arch) (Value arch ids)
                         -> BlockStartStackConstraints arch
postCallStackConstraints params cns regs =
  runNextStateMonad $ do
    rm <- MapF.traverseMaybeWithKey (postCallConstraint params cns) (regStateMap regs)

    let finalStack = stackExprMap cns
    let filteredStack =
          case blockIntraValueExpr cns (getBoundValue sp_reg regs) of
            StackOffsetExpr spOff
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
                    -> StackExpr arch ids tp
                    -> NextStateMonad arch ids (Maybe (StackEqConstraint (ArchReg arch) tp))
        nextStackFn i repr e =
          nextStateStackEqConstraint (StackOffLoc i repr) e

    sm <- stackMapTraverseMaybeWithKey nextStackFn filteredStack

    pure $! BSSC (LocMap { locMapRegs = rm, locMapStack = sm })
