{-|
Defines data types needed to represent values, assignments, and statements from Machine code.

This is a low-level CFG representation where the entire program is a
single CFG.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.CFG.Core
  ( -- * Stmt level declarations
    Stmt(..)
  , Assignment(..)
  , AssignId(..)
    -- * Value
  , Value(..)
  , CValue(..)
  , pattern BoolValue
  , pattern BVValue
  , pattern RelocatableValue
  , pattern SymbolValue
  , BVValue
  , valueAsApp
  , valueAsArchFn
  , valueAsRhs
  , valueAsMemAddr
  , valueAsSegmentOff
  , valueAsStaticMultiplication
  , StackOffsetView(..)
  , appAsStackOffset
  , asBaseOffset
  , asInt64Constant
  , IPAlignment(..)
  , mkLit
  , bvValue
  , ppValueAssignments
  , ppValueAssignmentList
  -- * RegState
  , RegState
  , regStateMap
  , getBoundValue
  , boundValue
  , cmpRegState
  , curIP
  , mkRegState
  , mkRegStateM
  , mapRegsWith
  , traverseRegsWith
  , traverseRegsWith_
  , zipWithRegState
  , ppRegMap
  -- * Pretty printing
  , ppAssignId
  , ppValue
  , ppStmt
  , PrettyF(..)
  , ArchConstraints
  , PrettyRegValue(..)
  , IsArchFn(..)
  , IsArchStmt(..)
    -- * Utilities
  , addrWidthTypeRepr
    -- * RegisterInfo
  , RegisterInfo(..)
  , asStackAddrOffset
    -- * References
  , refsInValue
    -- ** Synonyms
  , ArchAddrValue
  , Data.Parameterized.TraversableFC.FoldableFC(..)
  , module Data.Macaw.CFG.AssignRhs
  , module Data.Macaw.Utils.Pretty
  ) where

import           Control.Lens
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Int (Int64)
import qualified Data.Kind as Kind
import           Data.Maybe (isNothing, catMaybes)
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC (FoldableFC(..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.TypeLits
import           Numeric (showHex)
import           Numeric.Natural
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))

import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.AssignRhs
import           Data.Macaw.Memory
import           Data.Macaw.Types
import           Data.Macaw.Utils.Pretty

-- Note:
-- The declarations in this file follow a top-down order, so the top-level
-- definitions should be first.

type Prec = Int

colonPrec :: Prec
colonPrec = 7

plusPrec :: Prec
plusPrec = 6

-- | Class for pretty printing with a precedence field.
class PrettyPrec v where
  prettyPrec :: Int -> v -> Doc

-- | Pretty print over all instances of a type.
class PrettyF (f :: k -> Kind.Type) where
  prettyF :: f tp -> Doc

-- | Pretty print a document with parens if condition is true
parenIf :: Bool -> Doc -> Doc
parenIf True d = parens d
parenIf False d = d

bracketsep :: [Doc] -> Doc
bracketsep [] = text "{}"
bracketsep (h:l) = vcat $
  [text "{" <+> h]
  ++ fmap (text "," <+>) l
  ++ [text "}"]

-- | A type repr for the address width
addrWidthTypeRepr :: AddrWidthRepr w -> TypeRepr (BVType w)
addrWidthTypeRepr Addr32 = BVTypeRepr knownNat
addrWidthTypeRepr Addr64 = BVTypeRepr knownNat

------------------------------------------------------------------------
-- AssignId

-- | An 'AssignId' is a unique identifier used to identify assignment
-- statements, in a manner similar to SSA (single static assignment)
-- form. 'AssignId's are typed, and also include a type variable @ids@
-- that intuitively denotes the set of identifiers from which they are
-- drawn.
newtype AssignId (ids :: Kind.Type) (tp :: Type) = AssignId (Nonce ids tp)

ppAssignId :: AssignId ids tp -> Doc
ppAssignId (AssignId w) = text ("r" ++ show (indexValue w))

instance Eq (AssignId ids tp) where
  AssignId id1 == AssignId id2 = id1 == id2

instance TestEquality (AssignId ids) where
  testEquality (AssignId id1) (AssignId id2) = testEquality id1 id2

instance Ord (AssignId ids tp) where
  compare (AssignId x) (AssignId y) = compare x y

instance OrdF (AssignId ids) where
  compareF (AssignId id1) (AssignId id2) = compareF id1 id2

instance Show (AssignId ids tp) where
  show (AssignId n) = show (indexValue n)

instance ShowF (AssignId ids) where
  showF = show

------------------------------------------------------------------------
-- CValue

-- | A constant whose value does not change during execution.
data CValue arch tp where
  -- | A constant bitvector
  --
  -- The integer should be between 0 and 2^n-1.
  BVCValue :: (1 <= n) => !(NatRepr n) -> !Integer -> CValue arch (BVType n)
  -- | A constant Boolean
  BoolCValue :: !Bool -> CValue arch BoolType
  -- | A memory address
  RelocatableCValue :: !(AddrWidthRepr (ArchAddrWidth arch))
                    -> !(MemAddr (ArchAddrWidth arch))
                    -> CValue arch (BVType (ArchAddrWidth arch))
  -- | This denotes the address of a symbol identifier in the binary.
  --
  -- This appears when dealing with relocations.
  SymbolCValue :: !(AddrWidthRepr (ArchAddrWidth arch))
               -> !SymbolIdentifier
               -> CValue arch (BVType (ArchAddrWidth arch))

instance TestEquality (CValue arch) where
  testEquality (BVCValue xw xi) (BVCValue yw yi) = do
    Refl <- testEquality xw yw
    if xi == yi then Just Refl else Nothing
  testEquality (BoolCValue x) (BoolCValue y) = do
    if x == y then Just Refl else Nothing
  testEquality (RelocatableCValue _ x) (RelocatableCValue _ y) = do
    if x == y then Just Refl else Nothing
  testEquality (SymbolCValue _ x) (SymbolCValue _ y) = do
    if x == y then Just Refl else Nothing
  testEquality _ _ = Nothing

instance OrdF (CValue arch) where
  compareF (BoolCValue x) (BoolCValue y) = fromOrdering (compare x y)
  compareF BoolCValue{} _ = LTF
  compareF _ BoolCValue{} = GTF

  compareF (BVCValue wx vx) (BVCValue wy vy) =
    case compareF wx wy of
      LTF -> LTF
      EQF -> fromOrdering (compare vx vy)
      GTF -> GTF
  compareF BVCValue{} _ = LTF
  compareF _ BVCValue{} = GTF

  compareF (RelocatableCValue _ x) (RelocatableCValue _ y) =
    fromOrdering (compare x y)
  compareF RelocatableCValue{} _ = LTF
  compareF _ RelocatableCValue{} = GTF

  compareF (SymbolCValue _ x) (SymbolCValue _ y) =
    fromOrdering (compare x y)

instance HasRepr (CValue arch) TypeRepr where
  typeRepr (BoolCValue _) = BoolTypeRepr
  typeRepr (BVCValue w _) = BVTypeRepr w
  typeRepr (RelocatableCValue w _) = addrWidthTypeRepr w
  typeRepr (SymbolCValue w _)      = addrWidthTypeRepr w

instance Hashable (CValue arch tp) where
  hashWithSalt s cv =
    case cv of
      BVCValue w i          -> s `hashWithSalt` (0::Int) `hashWithSalt` w `hashWithSalt` i
      BoolCValue b          -> s `hashWithSalt` (1::Int) `hashWithSalt` b
      RelocatableCValue _ a -> s `hashWithSalt` (2::Int) `hashWithSalt` a
      SymbolCValue _ sym    -> s `hashWithSalt` (3::Int) `hashWithSalt` sym

instance HashableF (CValue arch) where
  hashWithSaltF = hashWithSalt

------------------------------------------------------------------------
-- Value and Assignment

-- | A value at runtime.
data Value arch ids tp where
  CValue :: !(CValue arch tp) -> Value arch ids tp
  -- | Value from an assignment statement.
  AssignedValue :: !(Assignment arch ids tp)
                -> Value arch ids tp
  -- | Represents the value assigned to the register when the block started.
  Initial :: !(ArchReg arch tp)
          -> Value arch ids tp

-- | A constant bitvector
--
-- The integer should be between 0 and 2^n-1.
pattern BVValue :: ()
                => forall n . (tp ~ (BVType n), 1 <= n)
                => NatRepr n
                -> Integer
                -> Value arch ids tp
pattern BVValue w i = CValue (BVCValue w i)

-- | A constant Boolean
pattern BoolValue :: () => (tp ~ BoolType) => Bool -> Value arch ids tp
pattern BoolValue b = CValue (BoolCValue b)

-- | A memory address
pattern RelocatableValue :: ()
                         => tp ~ BVType (ArchAddrWidth arch)
                         => AddrWidthRepr (ArchAddrWidth arch)
                         -> MemAddr (ArchAddrWidth arch)
                         -> Value arch ids tp
pattern RelocatableValue w a = CValue (RelocatableCValue w a)

-- | This denotes the address of a symbol identifier in the binary.
--
-- This appears when dealing with relocations.
pattern SymbolValue :: ()
                    => tp ~ BVType (ArchAddrWidth arch)
                    => AddrWidthRepr (ArchAddrWidth arch)
                    -> SymbolIdentifier
                    -> Value arch ids tp
pattern SymbolValue w s = CValue (SymbolCValue w s)

{-# COMPLETE BVValue, BoolValue, RelocatableValue, SymbolValue, AssignedValue, Initial #-}

-- | An assignment consists of a unique location identifier and a right-
-- hand side that returns a value.
data Assignment arch ids tp =
  Assignment { assignId :: !(AssignId ids tp)
             , assignRhs :: !(AssignRhs arch (Value arch ids) tp)
             }

-- | A  value with a bitvector type.
type BVValue arch ids w = Value arch ids (BVType w)

-- | A address value for a specific architecture
type ArchAddrValue arch ids = BVValue arch ids (ArchAddrWidth arch)

------------------------------------------------------------------------
-- Type operations on assignment Value

instance HasRepr (ArchReg arch) TypeRepr
      => HasRepr (Value arch ids) TypeRepr where

  typeRepr (CValue c) = typeRepr c
  typeRepr (AssignedValue a) = typeRepr (assignRhs a)
  typeRepr (Initial r) = typeRepr r

------------------------------------------------------------------------
-- Value equality

instance OrdF (ArchReg arch)
      => OrdF (Value arch ids) where

  compareF (CValue x) (CValue y) = compareF x y
  compareF CValue{} _ = LTF
  compareF _ CValue{} = GTF

  compareF (AssignedValue x) (AssignedValue y) =
    compareF (assignId x) (assignId y)
  compareF AssignedValue{} _ = LTF
  compareF _ AssignedValue{} = GTF

  compareF (Initial r) (Initial r') =
    case compareF r r' of
      LTF -> LTF
      EQF -> EQF
      GTF -> GTF

instance OrdF (ArchReg arch)
      => TestEquality (Value arch ids) where
  testEquality x y = orderingF_refl (compareF x y)

instance OrdF (ArchReg arch)
      => Eq  (Value arch ids tp) where
  x == y = isJust (testEquality x y)

instance OrdF (ArchReg arch)
      => Ord (Value arch ids tp) where
  compare x y = toOrdering (compareF x y)

instance OrdF (ArchReg arch)
      => EqF (Value arch ids) where
  eqF = (==)

------------------------------------------------------------------------
-- Value operations

mkLit :: (1 <= n) => NatRepr n -> Integer -> Value arch ids (BVType n)
mkLit n v = BVValue n (v .&. mask)
  where mask = maxUnsigned n

bvValue :: (KnownNat n, 1 <= n) => Integer -> Value arch ids (BVType n)
bvValue i = mkLit knownNat i

-- | Return the right-hand side if this is an assignment.
valueAsRhs :: Value arch ids tp -> Maybe (AssignRhs arch (Value arch ids) tp)
valueAsRhs (AssignedValue (Assignment _ v)) = Just v
valueAsRhs _ = Nothing

-- | Return the value evaluated if this is from an `App`.
valueAsApp :: Value arch ids tp -> Maybe (App (Value arch ids) tp)
valueAsApp (AssignedValue (Assignment _ (EvalApp a))) = Just a
valueAsApp _ = Nothing

-- | Return the architecture-specific function associated with a value.
valueAsArchFn :: Value arch ids tp -> Maybe (ArchFn arch (Value arch ids) tp)
valueAsArchFn (AssignedValue (Assignment _ (EvalArchFn a _))) = Just a
valueAsArchFn _ = Nothing

-- | This returns a segmented address if the value can be interpreted as a literal memory
-- address, and returns nothing otherwise.
valueAsMemAddr :: MemWidth (ArchAddrWidth arch)
               => BVValue arch ids (ArchAddrWidth arch)
               -> Maybe (ArchMemAddr arch)
valueAsMemAddr (BVValue _ val)      = Just $ absoluteAddr (fromInteger val)
valueAsMemAddr (RelocatableValue _ i) = Just i
valueAsMemAddr _ = Nothing

valueAsStaticMultiplication
  :: BVValue arch ids w
  -> Maybe (Natural, BVValue arch ids w)
valueAsStaticMultiplication v
  | Just (BVMul _ (BVValue _ mul) v') <- valueAsApp v = Just (fromInteger mul, v')
  | Just (BVMul _ v' (BVValue _ mul)) <- valueAsApp v = Just (fromInteger mul, v')
  | Just (BVShl _ v' (BVValue _ sh))  <- valueAsApp v = Just (2^sh, v')
  -- the PowerPC way to shift left is a bit obtuse...
  | Just (BVAnd w v' (BVValue _ c)) <- valueAsApp v
  , Just (BVOr _ l r) <- valueAsApp v'
  , Just (BVShl _ l' (BVValue _ shl)) <- valueAsApp l
  , Just (BVShr _ _ (BVValue _ shr)) <- valueAsApp r
  , c == complement (2^shl-1) `mod` bit (fromInteger (intValue w))
  , shr >= intValue w - shl
  = Just (2^shl, l')
  | otherwise = Nothing

-- | Returns a segment offset associated with the value if one can be defined.
valueAsSegmentOff :: Memory (ArchAddrWidth arch)
                  -> BVValue arch ids (ArchAddrWidth arch)
                  -> Maybe (ArchSegmentOff arch)
valueAsSegmentOff mem v = do
  a <- addrWidthClass (memAddrWidth mem) (valueAsMemAddr v)
  asSegmentOff mem a

asInt64Constant :: Value arch ids (BVType 64) -> Maybe Int64
asInt64Constant (BVValue _ o) = Just (fromInteger o)
asInt64Constant _ = Nothing

asBaseOffset :: Value arch ids (BVType w) -> (Value arch ids (BVType w), Integer)
asBaseOffset x
  | Just (BVAdd _ x_base (BVValue _  x_off)) <- valueAsApp x = (x_base, x_off)
  | otherwise = (x,0)

-- | A stack offset that can also capture the width must match the pointer width.
data StackOffsetView arch tp where
  StackOffsetView :: !Integer -> StackOffsetView arch (BVType (ArchAddrWidth arch))

-- | This pattern matches on an app to see if it can be used to adjust a
-- stack offset.
appAsStackOffset :: forall arch ids tp
                 .  MemWidth (ArchAddrWidth arch)
                 => (Value arch ids (BVType (ArchAddrWidth arch)) -> Maybe Integer)
                 -- ^ Function for inferring if argument is a stack offset.
                 -> App (Value arch ids) tp
                 -> Maybe (StackOffsetView arch tp)
appAsStackOffset stackFn app =
  case app of
    BVAdd w (BVValue _ i) y -> do
      Refl <- testEquality w (memWidthNatRepr @(ArchAddrWidth arch))
      (\j -> StackOffsetView (i+j)) <$> stackFn y
    BVAdd w x (BVValue _ j) -> do
      Refl <- testEquality w (memWidthNatRepr @(ArchAddrWidth arch))
      (\i -> StackOffsetView (i+j)) <$> stackFn x
    BVSub w x (BVValue _ j) -> do
      Refl <- testEquality w (memWidthNatRepr @(ArchAddrWidth arch))
      (\i -> StackOffsetView (i-j)) <$> stackFn x
    _ ->
      Nothing

-- | During the jump-table detection phase of code discovery, we have the
-- following problem: we are given a value which represents the computation
-- done to create an address to jump to. We'd like to look at the shape of that
-- computation and check whether it "looks like a jump table" -- say, whether
-- it is the computation @array_base + pointer_size * i@ for some unknown index
-- @i@.
--
-- However, some architectures have special rules about what addresses are
-- valid jump targets, and so there is frequently a sort of "standard prelude"
-- which converts an arbitrary address into a valid jump target. For example,
-- on PowerPC, the instruction pointer is always a multiple of four, so any
-- computed jump strips off the bottom two bits. We'd like the jump-table
-- detection code to be able to ignore that standard prelude when looking for
-- jump-table-like computations (without having to know that the right thing to
-- look for is "ignore the bottom two bits").
--
-- The 'fromIPAligned' method below gives specific architectures a hook for
-- stripping away the prelude and leaving the underlying computed value (which
-- is potentially an invalid jump target!).
--
-- Of course, after stripping away the cleanup parts of the computation,
-- checking the unclean computation for specific patterns, and finding
-- particular concrete values that the unclean computation could evaluate to,
-- the discovery code then needs to be able to re-clean the concrete values.
-- The 'toIPAligned' method gives architectures a hook to do that direction of
-- translation.
class IPAlignment arch where
  -- | Take an aligned value and strip away the bits of the semantics that
  -- align it, leaving behind a (potentially unaligned) value. Return 'Nothing'
  -- if the input value does not appear to be a valid value for the instruction
  -- pointer.
  fromIPAligned :: ArchAddrValue arch ids -> Maybe (ArchAddrValue arch ids)

  -- | Take an unaligned memory address and clean it up so that it is a valid
  -- value for the instruction pointer.
  toIPAligned :: MemAddr (ArchAddrWidth arch) -> MemAddr (ArchAddrWidth arch)

------------------------------------------------------------------------
-- RegState

-- | This represents the state of the processor registers.
newtype RegState (r :: k -> Kind.Type) (f :: k -> Kind.Type) = RegState (MapF.MapF r f)

deriving instance (OrdF r, EqF f) => Eq (RegState r f)

deriving instance FunctorF  (RegState r)
deriving instance FoldableF (RegState r)

instance TraversableF (RegState r) where
  traverseF f (RegState m) = RegState <$> traverseF f m

-- | Return underlying map of register state.
regStateMap :: RegState r f -> MapF.MapF r f
regStateMap (RegState m) = m

-- | Traverse the register state with the name of each register and value.
traverseRegsWith :: Applicative m
                 => (forall tp. r tp -> f tp -> m (g tp))
                 -> RegState r f
                 -> m (RegState r g)
traverseRegsWith f (RegState m) = RegState <$> MapF.traverseWithKey f m

-- | Traverse the register state with the name of each register and value.
traverseRegsWith_ :: Applicative m
                  => (forall tp. r tp -> f tp -> m ())
                  -> RegState r f
                  -> m ()
traverseRegsWith_ f (RegState m) = MapF.traverseWithKey_ f m

-- | Traverse the register state with the name of each register and value.
mapRegsWith :: (forall tp. r tp -> f tp -> g tp)
            -> RegState r f
            -> RegState r g
mapRegsWith f (RegState m) = RegState (MapF.mapWithKey f m)

{-# INLINE[1] boundValue #-} -- Make sure the RULE gets a chance to fire

-- | Get a register out of the state.
boundValue :: forall r f tp
           .  OrdF r
           => r tp
           -> Simple Lens (RegState r f) (f tp)
boundValue r =
  -- TODO Ideally there would be a Lens-aware "alter"-type operation
  -- in Data.Parameterized.Map (see Data.Map source); such an
  -- operation would have SPECIALIZE pragmas that would make it good
  -- to use to implement this.  We're resorting to RULES here, without
  -- which boundValue was accounting for over 8% of runtime on
  -- Brittle.
  lens (getBoundValue r) (setBoundValue r)

getBoundValue :: OrdF r => r tp -> RegState r f -> f tp
getBoundValue r (RegState m) =
  case MapF.lookup r m of
    Just v -> v
    Nothing -> error "internal error in boundValue given unexpected reg"

-- Without this rule, boundValue gets left as a higher-order function,
-- making its uses VERY slow.
{-# RULES
      "boundValue/get" forall rs r. get (boundValue r) rs = getBoundValue r rs
  #-}
-- Note that this rule seems to cover (^.) as well as get, which is
-- fortunate since a parsing bug makes it impossible to mention (^.)
-- in a rule.

setBoundValue :: OrdF r => r tp -> RegState r f -> f tp -> RegState r f
setBoundValue r (RegState m) v = RegState (MapF.insert r v m)

-- | Compares if two register states are equal.
cmpRegState :: OrdF r
            => (forall u. f u -> g u -> Bool)
               -- ^ Function for checking if two values are equal.
            -> RegState r f
            -> RegState r g
            -> Bool
cmpRegState p (RegState x) (RegState y) = go (MapF.toList x) (MapF.toList y)
  where go [] [] = True
        go [] (_:_) = False
        go (_:_) [] = False
        go (MapF.Pair xk xv:xr) (MapF.Pair yk yv:yr) =
          case testEquality xk yk of
            Nothing -> False
            Just Refl -> p xv yv && go xr yr

------------------------------------------------------------------------
-- RegisterInfo

-- | This class provides access to information about registers.
class ( OrdF r
      , ShowF r
      , MemWidth (RegAddrWidth r)
      , HasRepr r  TypeRepr
      ) => RegisterInfo r where

  -- | List of all arch registers.
  archRegs :: [Some r]

  -- | Set of all arch registers (expressed as a 'MapF.Map' of units).
  -- Preferable to 'archRegs' when building a map.
  archRegSet :: MapF.MapF r (Const ())
  archRegSet = MapF.fromList [ MapF.Pair r (Const ()) | Some r <- archRegs ]

  -- | The stack pointer register
  sp_reg :: r (BVType (RegAddrWidth r))

  -- | The instruction pointer register
  ip_reg :: r (BVType (RegAddrWidth r))

  -- | The register used to store system call numbers.
  syscall_num_reg :: r (BVType (RegAddrWidth r))

  -- | Registers used for passing system call arguments
  syscallArgumentRegs :: [r (BVType (RegAddrWidth r))]

--  The value of the current instruction pointer.
curIP :: RegisterInfo r
      => Simple Lens (RegState r f) (f (BVType (RegAddrWidth r)))
curIP = boundValue ip_reg

mkRegStateM :: (RegisterInfo r, Applicative m)
            => (forall tp . r tp -> m (f tp))
            -> m (RegState r f)
mkRegStateM f = RegState <$> MapF.traverseWithKey (\k _ -> f k) archRegSet

-- Create a pure register state
mkRegState :: RegisterInfo r
           => (forall tp . r tp -> f tp)
           -> RegState r f
mkRegState f = runIdentity (mkRegStateM (return . f))

zipWithRegState :: RegisterInfo r
                => (forall u. f u -> g u -> h u)
                -> RegState r f
                -> RegState r g
                -> RegState r h
zipWithRegState f x y = mkRegState (\r -> f (x ^. boundValue r) (y ^. boundValue r))

-- | Returns a offset if the value is an offset of the stack.
asStackAddrOffset :: RegisterInfo (ArchReg arch)
                  => Value arch ids tp
                  -> Maybe (BVValue arch ids (ArchAddrWidth arch))
asStackAddrOffset addr
  | Just (BVAdd _ (Initial base) offset) <- valueAsApp addr
  , Just Refl <- testEquality base sp_reg = do
    Just offset
  | Initial base <- addr
  , Just Refl <- testEquality base sp_reg =
      case typeRepr base of
        BVTypeRepr w -> Just (BVValue w 0)
  | otherwise =
    Nothing

------------------------------------------------------------------------
-- Pretty print Assign, AssignRhs, Value operations

ppLit :: NatRepr n -> Integer -> Doc
ppLit w i
  | i >= 0 = text ("0x" ++ showHex i "") <+> text "::" <+> brackets (text (show w))
  | otherwise = error "ppLit given negative value"

-- | Pretty print a value.
ppValue :: RegisterInfo (ArchReg arch) => Prec -> Value arch ids tp -> Doc
ppValue _ (BoolValue b)     = text $ if b then "true" else "false"
ppValue p (BVValue w i)
  | i >= 0 = parenIf (p > colonPrec) $ ppLit w i
  | otherwise =
    -- TODO: We may want to report an error here.
    parenIf (p > colonPrec) $
    text (show i) <+> text "::" <+> brackets (text (show w))
ppValue p (RelocatableValue _ a) = parenIf (p > plusPrec) $ text (show a)
ppValue _ (SymbolValue _ a) = text (show a)
ppValue _ (AssignedValue a) = ppAssignId (assignId a)
ppValue _ (Initial r)       = text (showF r) PP.<> text "_0"

instance RegisterInfo (ArchReg arch) => PrettyPrec (Value arch ids tp) where
  prettyPrec = ppValue

instance RegisterInfo (ArchReg arch) => Pretty (Value arch ids tp) where
  pretty = ppValue 0

instance RegisterInfo (ArchReg arch) => Show (Value arch ids tp) where
  show = show . pretty

-- | Typeclass for architecture-specific functions
class IsArchFn (f :: (Type -> Kind.Type) -> Type -> Kind.Type)  where
  -- | A function for pretty printing an archFn of a given type.
  ppArchFn :: Applicative m
           => (forall u . v u -> m Doc)
              -- ^ Function for pretty printing vlaue.
           -> f v tp
           -> m Doc

-- | Typeclass for architecture-specific statements
class IsArchStmt (f :: (Type -> Kind.Type) -> Kind.Type)  where
  -- | A function for pretty printing an architecture statement of a given type.
  ppArchStmt :: (forall u . v u -> Doc)
                -- ^ Function for pretty printing value.
             -> f v
             -> Doc

-- | Constructs expected by architectures type classes.
type ArchConstraints arch
   = ( RegisterInfo (ArchReg arch)
     , FoldableFC (ArchFn arch)
     , IsArchFn   (ArchFn arch)
     , IsArchStmt (ArchStmt arch)
     , FoldableF  (ArchStmt arch)
     , PrettyF    (ArchTermStmt arch)
     , IPAlignment arch
     )

-- | Pretty print an assignment right-hand side using operations parameterized
-- over an application to allow side effects.
ppAssignRhs :: (Applicative m, ArchConstraints arch)
            => (forall u . f u -> m Doc)
               -- ^ Function for pretty printing value.
            -> AssignRhs arch f tp
            -> m Doc
ppAssignRhs pp (EvalApp a) = ppAppA pp a
ppAssignRhs _  (SetUndefined tp) = pure $ text "undef ::" <+> brackets (text (show tp))
ppAssignRhs pp (ReadMem a repr) =
  (\d -> text "read_mem" <+> d <+> PP.parens (pretty repr)) <$> pp a
ppAssignRhs pp (CondReadMem repr c a d) = f <$> pp c <*> pp a <*> pp d
  where f cd ad dd = text "cond_read_mem" <+> PP.parens (pretty repr) <+> cd <+> ad <+> dd
ppAssignRhs pp (EvalArchFn f _) = ppArchFn pp f

instance ArchConstraints arch => Pretty (AssignRhs arch (Value arch ids) tp) where
  pretty = runIdentity . ppAssignRhs (Identity . ppValue 10)

instance ArchConstraints arch => Pretty (Assignment arch ids tp) where
  pretty (Assignment lhs rhs) = ppAssignId lhs <+> text ":=" <+> pretty rhs

------------------------------------------------------------------------
-- Pretty print a value assignment

-- | Helper type to wrap up a 'Doc' with a dummy type argument; used to put
-- 'Doc's into heterogenous maps in the below
newtype DocF (a :: Type) = DocF Doc

-- | This pretty prints a value's representation while saving the pretty
-- printed repreentation of subvalues in a map.
collectValueRep :: forall arch ids tp
                .  ArchConstraints arch
                => Prec
                -> Value arch ids tp
                -> State (MapF (AssignId ids) DocF) Doc
collectValueRep _ (AssignedValue a) = do
  let lhs = assignId a
  mr <- gets $ MapF.lookup lhs
  when (isNothing mr) $ do
    let ppVal :: forall u . Value arch ids u ->
                 State (MapF (AssignId ids) DocF) Doc
        ppVal = collectValueRep 10
    rhs <- ppAssignRhs ppVal (assignRhs a)
    let d = ppAssignId lhs <+> text ":=" <+> rhs
    modify $ MapF.insert lhs (DocF d)
    return ()
  return $! ppAssignId lhs
collectValueRep p v = return $ ppValue p v

-- | This pretty prints all the history used to create a value.
ppValueAssignments' :: State (MapF (AssignId ids) DocF) Doc -> Doc
ppValueAssignments' m =
  case MapF.elems bindings of
    [] -> rhs
    (Some (DocF h):r) ->
      let first               = text "let" PP.<+> h
          f (Some (DocF b))   = text "    " PP.<> b
       in vcat (first:fmap f r) <$$>
          text " in" PP.<+> rhs
  where (rhs, bindings) = runState m MapF.empty

-- | This pretty prints all the history used to create a value.
ppValueAssignments :: ArchConstraints arch => Value arch ids tp -> Doc
ppValueAssignments v = ppValueAssignments' (collectValueRep 0 v)

ppValueAssignmentList :: ArchConstraints arch => [Value arch ids tp] -> Doc
ppValueAssignmentList vals =
  ppValueAssignments' $ do
    brackets . hcat . punctuate comma
      <$> traverse (collectValueRep 0) vals

------------------------------------------------------------------------
-- Pretty printing RegState

-- | This class provides a way of optionally pretty printing the contents
-- of a register or omitting them.
class PrettyRegValue r (f :: Type -> Kind.Type) where
  -- | ppValueEq should return a doc if the contents of the given register
  -- should be printed, and Nothing if the contents should be ignored.
  ppValueEq :: r tp -> f tp -> Maybe Doc

ppRegMap :: forall r v . PrettyRegValue r v => MapF.MapF r v -> Doc
ppRegMap m = bracketsep $ catMaybes (f <$> MapF.toList m)
  where f :: MapF.Pair r v -> Maybe Doc
        f (MapF.Pair r v) = ppValueEq r v


instance ( PrettyRegValue r f)
      => Pretty (RegState r f) where
  pretty (RegState m) = ppRegMap m

instance ( PrettyRegValue r f
         )
      => Show (RegState r f) where
  show s = show (pretty s)

instance ( RegisterInfo r
         , r ~ ArchReg arch
         )
      => PrettyRegValue r (Value arch ids) where
  ppValueEq r (Initial r')
    | Just _ <- testEquality r r' = Nothing
  ppValueEq r v
    | otherwise   = Just $ text (showF r) <+> text "=" <+> pretty v

------------------------------------------------------------------------
-- Stmt

-- | A statement in our control flow graph language.
data Stmt arch ids
   = forall tp . AssignStmt !(Assignment arch ids tp)
   | forall tp . WriteMem !(ArchAddrValue arch ids) !(MemRepr tp) !(Value arch ids tp)
     -- ^ This denotes a write to memory, and consists of an address
     -- to write to, a `MemRepr` defining how the value should be
     -- stored in memory, and the value to be written.
  | forall tp .
    CondWriteMem !(Value arch ids BoolType)
                 !(ArchAddrValue arch ids)
                 !(MemRepr tp)
                 !(Value arch ids tp)
     -- ^ This denotes a write to memory that only executes if the
     -- condition is true.
   | InstructionStart !(ArchAddrWord arch) !Text
     -- ^ The start of an instruction
     --
     -- The information includes the offset relative to the start of
     -- the block and the disassembler output if available (or empty
     -- string if unavailable)
   | Comment !Text
     -- ^ A user-level comment
   | ExecArchStmt !(ArchStmt arch (Value arch ids))
     -- ^ Execute an architecture specific statement
   | ArchState !(ArchMemAddr arch) !(MapF.MapF (ArchReg arch) (Value arch ids))
     -- ^ Address of an instruction and the *machine* registers that
     -- it updates (with their associated macaw values after the
     -- execution of the instruction).

ppStmt :: ArchConstraints arch
       => (ArchAddrWord arch -> Doc)
          -- ^ Function for pretty printing an instruction address offset
       -> Stmt arch ids
       -> Doc
ppStmt ppOff stmt =
  case stmt of
    AssignStmt a -> pretty a
    WriteMem     a _ rhs ->
      text "write_mem" <+> prettyPrec 11 a <+> ppValue 0 rhs
    CondWriteMem c a _ rhs ->
      text "cond_write_mem" <+> prettyPrec 11 c <+> prettyPrec 11 a
        <+> ppValue 0 rhs
    InstructionStart off mnem -> text "#" <+> ppOff off <+> text (Text.unpack mnem)
    Comment s -> text $ "# " ++ Text.unpack s
    ExecArchStmt s -> ppArchStmt (ppValue 10) s
    ArchState a m ->
        hang (length (show prefix)) (prefix PP.<> PP.semiBraces (MapF.foldrWithKey ppUpdate [] m))
      where
      ppAddr addr =
        case asAbsoluteAddr addr of
          Just absAddr -> text (show absAddr)
          Nothing -> PP.braces (PP.int (addrBase addr)) PP.<> text "+" PP.<> text (show (addrOffset addr))
      prefix = text "#" <+> ppAddr a PP.<> text ": "
      ppUpdate key val acc = text (showF key) <+> text "=>" <+> ppValue 0 val : acc

instance ArchConstraints arch => Show (Stmt arch ids) where
  show = show . ppStmt (\w -> text (show w))

------------------------------------------------------------------------
-- References

refsInValue :: Value arch ids tp -> Set (Some (AssignId ids))
refsInValue (AssignedValue (Assignment v _)) = Set.singleton (Some v)
refsInValue _                                = Set.empty
