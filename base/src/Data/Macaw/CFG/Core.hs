{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Defines data types needed to represent values, assignments, and statements from Machine code.

This is a low-level CFG representation where the entire program is a
single CFG.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.CFG.Core
  ( -- * Stmt level declarations
    Stmt(..)
  , Assignment(..)
  , AssignId(..)
  , AssignRhs(..)
  , MemRepr(..)
  , memReprBytes
    -- * Value
  , Value(..)
  , BVValue
  , valueAsApp
  , valueAsArchFn
  , asLiteralAddr
  , asBaseOffset
  , asInt64Constant
  , mkLit
  , bvValue
  , ppValueAssignments
  , ppValueAssignmentList
  -- * RegState
  , RegState(..)
  , regStateMap
  , boundValue
  , cmpRegState
  , curIP
  , mkRegState
  , mkRegStateM
  , traverseRegsWith
  , zipWithRegState
  -- * Pretty printing
  , ppAssignId
  , ppLit
  , ppValue
  , ppStmt
  , PrettyF(..)
  , ArchConstraints
  , PrettyRegValue(..)
  , IsArchFn(..)
  , IsArchStmt(..)
    -- * Architecture type families
  , ArchFn
  , ArchReg
  , ArchStmt
  , ArchTermStmt
  , RegAddrWord
  , RegAddrWidth
    -- * RegisterInfo
  , RegisterInfo(..)
  , asStackAddrOffset
    -- * References
  , refsInValue
  , refsInApp
  , refsInAssignRhs
    -- ** Synonyms
  , ArchAddrWidth
  , ArchAddrValue
  , ArchAddrWord
  , ArchMemAddr
  , ArchSegmentOff
  , Data.Parameterized.TraversableFC.FoldableFC(..)
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Int (Int64)
import           Data.Maybe (isNothing, catMaybes)
import           Data.Monoid
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC (FoldableFC(..))
import           Data.Proxy
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           GHC.TypeLits
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>), (<>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Data.Macaw.CFG.App
import           Data.Macaw.Memory ( MemWord, MemWidth, MemAddr, MemSegmentOff, Endianness(..)
                                   , absoluteAddr)
import           Data.Macaw.Types

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
class PrettyF (f :: k -> *) where
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

------------------------------------------------------------------------
-- AssignId

-- | An 'AssignId' is a unique identifier used to identify assignment
-- statements, in a manner similar to SSA (single static assignment)
-- form. 'AssignId's are typed, and also include a type variable @ids@
-- that intuitively denotes the set of identifiers from which they are
-- drawn.
newtype AssignId (ids :: *) (tp :: Type) = AssignId (Nonce ids tp)

ppAssignId :: AssignId ids tp -> Doc
ppAssignId (AssignId w) = text ("r" ++ show (indexValue w))

instance Eq (AssignId ids tp) where
  AssignId id1 == AssignId id2 = id1 == id2

instance TestEquality (AssignId ids) where
  testEquality (AssignId id1) (AssignId id2) = testEquality id1 id2

instance OrdF (AssignId ids) where
  compareF (AssignId id1) (AssignId id2) = compareF id1 id2

instance ShowF (AssignId ids) where
  showF (AssignId n) = show n

instance Show (AssignId ids tp) where
  show (AssignId n) = show n

------------------------------------------------------------------------
-- Type families for architecture specific components.

-- | Width of register used to store addresses.
type family RegAddrWidth (r :: Type -> *) :: Nat

-- | A word for the given architecture register type.
type RegAddrWord r = MemWord (RegAddrWidth r)

-- | Type family for defining what a "register" is for this architecture.
--
-- Registers include things like the general purpose registers, any flag
-- registers that can be read and written without side effects,
type family ArchReg (arch :: *) :: Type -> *

-- | A type family for architecture specific functions.
--
-- These function may return a value.  They may depend on the current state of
-- the heap, but should not affect the processor state.
--
-- The function may depend on the set of registers defined so far, and the type
-- of the result.
type family ArchFn (arch :: *) :: (Type -> *) -> Type -> *

-- | A type family for defining architecture-specific statements.
--
-- The second type parameter is the ids phantom type used to provide
-- uniqueness of Nonce values that identify assignments.
type family ArchStmt (arch :: *) :: (Type -> *) -> *

-- | A type family for defining architecture-specific statements that
-- may have instruction-specific effects on control-flow and register state.
--
-- The second type parameter is the ids phantom type used to provide
-- uniqueness of Nonce values that identify assignments.
--
-- An architecture-specific terminal statement may have side effects and change register
-- values, it may or may not return to the current function.  If it does return to the
-- current function, it is assumed to be at most one location, and the block-translator
-- must provide that value at translation time.
type family ArchTermStmt (arch :: *) :: * -> *

-- | Number of bits in addreses for architecture.
type ArchAddrWidth arch = RegAddrWidth (ArchReg arch)

-- | A word for the given architecture bitwidth.
type ArchAddrWord arch = RegAddrWord (ArchReg arch)

-- | A segmented addr for a given architecture.
type ArchMemAddr arch = MemAddr (ArchAddrWidth arch)

-- | A pair containing a segment and valid offset within the segment.
type ArchSegmentOff arch = MemSegmentOff (ArchAddrWidth arch)

------------------------------------------------------------------------
-- MemRepr

-- | The type stored in memory.
--
-- The endianess indicates whether the address stores the most
-- or least significant byte.  The following indices either store
-- the next lower or higher bytes.
data MemRepr (tp :: Type) where
  BVMemRepr :: (1 <= w) => !(NatRepr w) -> !Endianness -> MemRepr (BVType (8*w))

instance Pretty (MemRepr tp) where
  pretty (BVMemRepr w BigEndian)    = text "bvbe" <+> text (show w)
  pretty (BVMemRepr w LittleEndian) = text "bvle" <+> text (show w)

instance Show (MemRepr tp) where
  show = show . pretty

-- | Return the number of bytes this takes up.
memReprBytes :: MemRepr tp -> Integer
memReprBytes (BVMemRepr x _) = natValue x

instance TestEquality MemRepr where
  testEquality (BVMemRepr xw xe) (BVMemRepr yw ye) =
    if xe == ye then do
      Refl <- testEquality xw yw
      Just Refl
     else
      Nothing

instance OrdF MemRepr where
  compareF (BVMemRepr xw xe) (BVMemRepr yw ye) =
    case compareF xw yw of
      LTF -> LTF
      GTF -> GTF
      EQF -> fromOrdering (compare xe ye)

instance HasRepr MemRepr TypeRepr where
  typeRepr (BVMemRepr w _) =
    let r = (natMultiply n8 w)
     in case leqMulPos (Proxy :: Proxy 8) w of
          LeqProof -> BVTypeRepr r

------------------------------------------------------------------------
-- AssignRhs

-- | The right hand side of an assignment is an expression that
-- returns a value.
data AssignRhs (arch :: *) (f :: Type -> *) tp where
  -- An expression that is computed from evaluating subexpressions.
  EvalApp :: !(App f tp)
          -> AssignRhs arch f tp

  -- An expression with an undefined value.
  SetUndefined :: !(TypeRepr tp)
               -> AssignRhs arch f tp

  -- Read memory at given location.
  ReadMem :: !(f (BVType (ArchAddrWidth arch)))
          -> !(MemRepr tp)
          -> AssignRhs arch f tp

  CondReadMem :: !(MemRepr tp)
              -> !(f BoolType)
              -> !(f (BVType (ArchAddrWidth arch)))
              -> !(f tp)
              -> AssignRhs arch f tp
  -- ^ @CondReadMem tp cond addr v@ reads from memory at the given address if the
  -- condition is true and returns the value if it false.

  -- Call an architecture specific function that returns some result.
  EvalArchFn :: !(ArchFn arch f tp)
             -> !(TypeRepr tp)
             -> AssignRhs arch f tp

instance HasRepr (AssignRhs arch f) TypeRepr where
  typeRepr rhs =
    case rhs of
      EvalApp a -> typeRepr a
      SetUndefined tp -> tp
      ReadMem _ tp -> typeRepr tp
      CondReadMem tp _ _ _ -> typeRepr tp
      EvalArchFn _ rtp -> rtp

instance FoldableFC (ArchFn arch) => FoldableFC (AssignRhs arch) where
  foldMapFC go v =
    case v of
      EvalApp a -> foldMapFC go a
      SetUndefined _w -> mempty
      ReadMem addr _ -> go addr
      CondReadMem _ c a d -> go c <> go a <> go d
      EvalArchFn f _ -> foldMapFC go f

------------------------------------------------------------------------
-- Value and Assignment, AssignRhs declarations.

-- | A value at runtime.
data Value arch ids tp
   = forall n
   . (tp ~ BVType n, 1 <= n)
   => BVValue !(NatRepr n) !Integer
     -- ^ A constant bitvector
   | (tp ~ BoolType)
   => BoolValue !Bool
     -- ^ A constant Boolean
   | ( tp ~ BVType (ArchAddrWidth arch)
     , 1 <= ArchAddrWidth arch
     )
   => RelocatableValue !(NatRepr (ArchAddrWidth arch)) !(ArchMemAddr arch)
     -- ^ A legal memory address
   | AssignedValue !(Assignment arch ids tp)
     -- ^ Value from an assignment statement.
   | Initial !(ArchReg arch tp)
     -- ^ Represents the value assigned to the register when the block started.

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
-- Type operations on assignment AssignRhs, and Value

instance ( HasRepr (ArchReg arch) TypeRepr
         )
      => HasRepr (Value arch ids) TypeRepr where

  typeRepr (BoolValue _) = BoolTypeRepr
  typeRepr (BVValue w _) = BVTypeRepr w
  typeRepr (RelocatableValue w _) = BVTypeRepr w
  typeRepr (AssignedValue a) = typeRepr (assignRhs a)
  typeRepr (Initial r) = typeRepr r

------------------------------------------------------------------------
-- Value equality

instance OrdF (ArchReg arch)
      => OrdF (Value arch ids) where

  compareF (BoolValue x) (BoolValue y) = fromOrdering (compare x y)
  compareF BoolValue{} _ = LTF
  compareF _ BoolValue{} = GTF

  compareF (BVValue wx vx) (BVValue wy vy) =
    case compareF wx wy of
      LTF -> LTF
      EQF -> fromOrdering (compare vx vy)
      GTF -> GTF
  compareF BVValue{} _ = LTF
  compareF _ BVValue{} = GTF


  compareF (RelocatableValue _ x) (RelocatableValue _ y) =
    fromOrdering (compare x y)
  compareF RelocatableValue{} _ = LTF
  compareF _ RelocatableValue{} = GTF

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

valueAsApp :: Value arch ids tp -> Maybe (App (Value arch ids) tp)
valueAsApp (AssignedValue (Assignment _ (EvalApp a))) = Just a
valueAsApp _ = Nothing

-- | Return the architecture-specific function associated with a value.
valueAsArchFn :: Value arch ids tp -> Maybe (ArchFn arch (Value arch ids) tp)
valueAsArchFn (AssignedValue (Assignment _ (EvalArchFn a _))) = Just a
valueAsArchFn _ = Nothing

-- | This returns a segmented address if the value can be interpreted as a literal memory
-- address, and returns nothing otherwise.
asLiteralAddr :: MemWidth (ArchAddrWidth arch)
              => BVValue arch ids (ArchAddrWidth arch)
              -> Maybe (ArchMemAddr arch)
asLiteralAddr (BVValue _ val)      = Just $ absoluteAddr (fromInteger val)
asLiteralAddr (RelocatableValue _ i) = Just i
asLiteralAddr _ = Nothing

asInt64Constant :: Value arch ids (BVType 64) -> Maybe Int64
asInt64Constant (BVValue _ o) = Just (fromInteger o)
asInt64Constant _ = Nothing

asBaseOffset :: Value arch ids (BVType w) -> (Value arch ids (BVType w), Integer)
asBaseOffset x
  | Just (BVAdd _ x_base (BVValue _  x_off)) <- valueAsApp x = (x_base, x_off)
  | otherwise = (x,0)

------------------------------------------------------------------------
-- RegState

-- | This represents the state of the processor registers.
newtype RegState (r :: k -> *) (f :: k -> *) = RegState (MapF.MapF r f)

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

-- | Get a register out of the state.
boundValue :: forall r f tp
           .  OrdF r
           => r tp
           -> Simple Lens (RegState r f) (f tp)
boundValue r = lens getter setter
  where getter (RegState m) =
          case MapF.lookup r m of
            Just v -> v
            Nothing -> error "internal error in boundValue given unexpected reg"
        setter (RegState m) v = RegState (MapF.insert r v m)


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
mkRegStateM f = RegState . MapF.fromList <$> traverse g archRegs
  where g (Some r) = MapF.Pair r <$> f r

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
ppValue p (BVValue w i)     = assert (i >= 0) $ parenIf (p > colonPrec) $ ppLit w i
ppValue p (RelocatableValue _ a) = parenIf (p > plusPrec) $ text (show a)
ppValue _ (AssignedValue a) = ppAssignId (assignId a)
ppValue _ (Initial r)       = text (showF r) PP.<> text "_0"

instance RegisterInfo (ArchReg arch) => PrettyPrec (Value arch ids tp) where
  prettyPrec = ppValue

instance RegisterInfo (ArchReg arch) => Pretty (Value arch ids tp) where
  pretty = ppValue 0

instance RegisterInfo (ArchReg arch) => Show (Value arch ids tp) where
  show = show . pretty

-- | Typeclass for architecture-specific functions
class IsArchFn (f :: (Type -> *) -> Type -> *)  where
  -- | A function for pretty printing an archFn of a given type.
  ppArchFn :: Applicative m
           => (forall u . v u -> m Doc)
              -- ^ Function for pretty printing vlaue.
           -> f v tp
           -> m Doc

-- | Typeclass for architecture-specific statements
class IsArchStmt (f :: (Type -> *) -> *)  where
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
  where f cd ad dd = text "read_mem" <+> PP.parens (pretty repr) <+> cd <+> ad <+> dd
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
class PrettyRegValue r (f :: Type -> *) where
  -- | ppValueEq should return a doc if the contents of the given register
  -- should be printed, and Nothing if the contents should be ignored.
  ppValueEq :: r tp -> f tp -> Maybe Doc

instance ( PrettyRegValue r f
         )
      => Pretty (RegState r f) where
  pretty (RegState m) = bracketsep $ catMaybes (f <$> MapF.toList m)
    where f :: MapF.Pair r f -> Maybe Doc
          f (MapF.Pair r v) = ppValueEq r v

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
     -- ^ This denotes a write to memory, and consists of an address to write to, a `MemRepr` defining
     -- how the value should be stored in memory, and the value to be written.
   | PlaceHolderStmt !([Some (Value arch ids)]) !String
     -- ^ A placeholder to indicate something the
     -- architecture-specific backend does not support.
     --
     -- Note that we plan to remove this eventually
   | InstructionStart !(ArchAddrWord arch) !Text
     -- ^ The start of an instruction
     --
     -- The information includes the offset relative to the start of the block and the
     -- disassembler output if available (or empty string if unavailable)
   | Comment !Text
     -- ^ A user-level comment
   | ExecArchStmt !(ArchStmt arch (Value arch ids))
     -- ^ Execute an architecture specific statement

ppStmt :: ArchConstraints arch
       => (ArchAddrWord arch -> Doc)
          -- ^ Function for pretty printing an offset
       -> Stmt arch ids
       -> Doc
ppStmt ppOff stmt =
  case stmt of
    AssignStmt a -> pretty a
    WriteMem a _ rhs -> text "*" PP.<> prettyPrec 11 a <+> text ":=" <+> ppValue 0 rhs
    PlaceHolderStmt vals name ->
      text ("PLACEHOLDER: " ++ name)
      <+> parens (hcat $ punctuate comma $ viewSome (ppValue 0) <$> vals)
    InstructionStart off mnem -> text "#" <+> ppOff off <+> text (Text.unpack mnem)
    Comment s -> text $ "# " ++ Text.unpack s
    ExecArchStmt s -> ppArchStmt (ppValue 10) s

instance ArchConstraints arch => Show (Stmt arch ids) where
  show = show . ppStmt (\w -> text (show w))

------------------------------------------------------------------------
-- References

refsInValue :: Value arch ids tp -> Set (Some (AssignId ids))
refsInValue (AssignedValue (Assignment v _)) = Set.singleton (Some v)
refsInValue _                                = Set.empty

refsInApp :: App (Value arch ids) tp -> Set (Some (AssignId ids))
refsInApp app = foldMapFC refsInValue app

refsInAssignRhs :: FoldableFC (ArchFn arch)
                => AssignRhs arch (Value arch ids) tp
                -> Set (Some (AssignId ids))
refsInAssignRhs rhs =
  case rhs of
    EvalApp v      -> refsInApp v
    SetUndefined _ -> Set.empty
    ReadMem v _    -> refsInValue v
    CondReadMem _ c a d ->
      Set.union (refsInValue c) $
      Set.union (refsInValue a) (refsInValue d)
    EvalArchFn f _ -> foldMapFC refsInValue f
