{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

Defines data types needed to represent control flow graphs from machine code.

This is a low-level CFG representation where the entire program is a
single CFG.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.CFG
  ( CFG
  , emptyCFG
  , cfgBlocks
  , insertBlocksForCode
  , traverseBlocks
  , traverseBlockAndChildren
  , findBlock
    -- * Block level declarations
  , BlockLabel(..)
  , isRootBlockLabel
  , rootBlockLabel
  , mkRootBlockLabel
  , Block(..)
    -- * Stmt level declarations
  , Stmt(..)
  , TermStmt(..)
  , Assignment(..)
  , AssignId(..)
  , AssignRhs(..)
  , MemRepr(..)
  , memReprBytes
    -- * Value
  , Value(..)
  , BVValue
  , valueAsApp
  , valueWidth
  , asBaseOffset
  , asInt64Constant
  , mkLit
  , bvValue
  , ppValueAssignments
  , ppValueAssignmentList
  -- * App
  , module Data.Macaw.CFG.App
  -- * RegState
  , RegState
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
  , PrettyF(..)
  , ArchConstraints(..)
  , PrettyRegValue(..)
    -- * Architecture type families
  , ArchAddr
  , ArchSegmentedAddr
  , ArchFn
  , ArchReg
  , ArchStmt
  , RegAddr
  , RegAddrWidth
    -- * RegisterInfo
  , RegisterInfo(..)
  , asStackAddrOffset
    -- * References
  , StmtHasRefs(..)
  , FnHasRefs(..)
  , refsInValue
  , refsInApp
  , refsInAssignRhs
    -- ** Synonyms
  , ArchAddrWidth
  , ArchLabel
  , ArchAddrValue
  , Data.Macaw.Memory.SegmentedAddr
  ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad.Identity
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Int (Int64)
import           Data.List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe (isNothing, catMaybes)
import           Data.Monoid as Monoid
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import           GHC.TypeLits
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.CFG.App
import           Data.Macaw.Memory (MemWord, MemWidth, SegmentedAddr(..), Endianness)
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
-- BlockLabel

-- | A label used to identify a block within a function.
--
-- The field is the address width.
data BlockLabel w
   = GeneratedBlock { labelAddr   :: !(SegmentedAddr w)
                      -- ^ Address of function label
                    , labelIndex  :: {-# UNPACK #-} !Word64
                    -- ^ A unique identifier for a generated block.
                    }
  deriving Eq

isRootBlockLabel :: BlockLabel w -> Bool
isRootBlockLabel (GeneratedBlock _ w) = w == 0

rootBlockLabel :: BlockLabel w -> BlockLabel w
rootBlockLabel (GeneratedBlock p _) = GeneratedBlock p 0

mkRootBlockLabel :: SegmentedAddr w -> BlockLabel w
mkRootBlockLabel p = GeneratedBlock p 0

instance Ord (BlockLabel w) where
  compare (GeneratedBlock p v) (GeneratedBlock p' v') =
    compare p p' Monoid.<> compare v v'

instance Show (BlockLabel w) where
  showsPrec _ (GeneratedBlock a 0) s = "block_" ++ shows a s
  showsPrec _ (GeneratedBlock a w) s = "subblock_" ++ shows a ("_" ++ shows w s)
  {-# INLINABLE showsPrec #-}

instance Pretty (BlockLabel w) where
  pretty l = text (show l)

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

-- | The value used to store
type RegAddr r = MemWord (RegAddrWidth r)

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
type family ArchFn (arch :: *) :: * -> Type -> *

-- | A type family for defining architecture-specific statements.
--
-- The second type parameter is the ids phantom type used to provide
-- uniqueness of Nonce values that identify assignments.
--
type family ArchStmt (arch :: *) :: * -> *

-- | The type to use for addresses on the architecutre.
type ArchAddr arch = RegAddr (ArchReg arch)

-- | Number of bits in addreses for architecture.
type ArchAddrWidth arch = RegAddrWidth (ArchReg arch)

-- | A segmented addr for a given architecture.
type ArchSegmentedAddr arch = SegmentedAddr (ArchAddrWidth arch)


type ArchLabel arch = BlockLabel (ArchAddrWidth arch)

------------------------------------------------------------------------
-- Value, Assignment, AssignRhs declarations.

-- | A value at runtime.
data Value arch ids tp
   = forall n
   .  (tp ~ BVType n)
   => BVValue !(NatRepr n) !Integer
     -- ^ A constant bitvector
   | ( tp ~ BVType (ArchAddrWidth arch))
   => RelocatableValue !(NatRepr (ArchAddrWidth arch)) !(MemWord (ArchAddrWidth arch))
     -- ^ A given memory address.
   | AssignedValue !(Assignment arch ids tp)
     -- ^ Value from an assignment statement.
   | Initial !(ArchReg arch tp)
     -- ^ Represents the value assigned to the register when the block started.

type BVValue arch ids w = Value arch ids (BVType w)

-- | A address value for a specific architecture
type ArchAddrValue arch ids = BVValue arch ids (ArchAddrWidth arch)

-- | An assignment consists of a unique location identifier and a right-
-- hand side that returns a value.
data Assignment arch ids tp =
  Assignment { assignId :: !(AssignId ids tp)
             , assignRhs :: !(AssignRhs arch ids tp)
             }

-- | The type stored in memory.
--
-- The endianess indicates whether the address stores the most
-- or least significant byte.  The following indices either store
-- the next lower or higher bytes.
data MemRepr (tp :: Type) where
  BVMemRepr :: NatRepr w -> Endianness -> MemRepr (BVType (8*w))

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

instance HasRepr MemRepr TypeRepr where
  typeRepr (BVMemRepr w _) = BVTypeRepr (natMultiply n8 w)

-- | The right hand side of an assignment is an expression that
-- returns a value.
data AssignRhs (arch :: *) ids tp where
  -- An expression that is computed from evaluating subexpressions.
  EvalApp :: !(App (Value arch ids) tp)
          -> AssignRhs arch ids tp

  -- An expression with an undefined value.
  SetUndefined :: (tp ~ BVType n)
               => !(NatRepr n) -- Width of undefined value.
               -> AssignRhs arch ids tp

  -- Read memory at given location.
  ReadMem :: !(ArchAddrValue arch ids)
          -> !(MemRepr tp)
          -> AssignRhs arch ids tp

  -- Call an architecture specific function that returns some result.
  EvalArchFn :: !(ArchFn arch ids tp)
             -> !(TypeRepr tp)
             -> AssignRhs arch ids tp

------------------------------------------------------------------------
-- Type operations on assignment AssignRhs, and Value

instance HasRepr (AssignRhs arch ids) TypeRepr where
  typeRepr rhs =
    case rhs of
      EvalApp a -> typeRepr a
      SetUndefined w -> BVTypeRepr w
      ReadMem _ tp -> typeRepr tp
      EvalArchFn _ rtp -> rtp

instance ( HasRepr (ArchReg arch) TypeRepr
         )
      => HasRepr (Value arch ids) TypeRepr where

  typeRepr (BVValue w _) = BVTypeRepr w
  typeRepr (RelocatableValue w _) = BVTypeRepr w
  typeRepr (AssignedValue a) = typeRepr (assignRhs a)
  typeRepr (Initial r) = typeRepr r

valueWidth :: ( HasRepr (ArchReg arch) TypeRepr
              )
           => Value arch ids (BVType n) -> NatRepr n
valueWidth v =
  case typeRepr v of
    BVTypeRepr n -> n

------------------------------------------------------------------------
-- Value equality

instance OrdF (ArchReg arch)
      => OrdF (Value arch ids) where
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

mkLit :: NatRepr n -> Integer -> Value arch ids (BVType n)
mkLit n v = BVValue n (v .&. mask)
  where mask = maxUnsigned n

bvValue :: KnownNat n => Integer -> Value arch ids (BVType n)
bvValue i = mkLit knownNat i

valueAsApp :: Value arch ids tp -> Maybe (App (Value arch ids) tp)
valueAsApp (AssignedValue (Assignment _ (EvalApp a))) = Just a
valueAsApp _ = Nothing

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
mkRegState :: RegisterInfo r -- AbsRegState r
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
ppValue :: ShowF (ArchReg arch) => Prec -> Value arch ids tp -> Doc
ppValue p (BVValue w i)     = assert (i >= 0) $ parenIf (p > colonPrec) $ ppLit w i
ppValue p (RelocatableValue _ a) = parenIf (p > plusPrec) $ text (show a)
ppValue _ (AssignedValue a) = ppAssignId (assignId a)
ppValue _ (Initial r)       = text (showF r) PP.<> text "_0"

instance ShowF (ArchReg arch) => PrettyPrec (Value arch ids tp) where
  prettyPrec = ppValue

instance ShowF (ArchReg arch) => Pretty (Value arch ids tp) where
  pretty = ppValue 0

instance ShowF (ArchReg arch) => Show (Value arch ids tp) where
  show = show . pretty

class ( RegisterInfo (ArchReg arch)
      , PrettyF  (ArchStmt arch)
      )  => ArchConstraints arch where

  -- | A function for pretty printing an archFn of a given type.
  ppArchFn :: Applicative m
           => (forall u . Value arch ids u -> m Doc)
              -- ^ Function for pretty printing vlaue.
           -> ArchFn arch ids tp
           -> m Doc

-- | Pretty print an assignment right-hand side using operations parameterized
-- over an application to allow side effects.
ppAssignRhs :: (Applicative m, ArchConstraints arch)
            => (forall u . Value arch ids u -> m Doc)
               -- ^ Function for pretty printing value.
            -> AssignRhs arch ids tp
            -> m Doc
ppAssignRhs pp (EvalApp a) = ppAppA pp a
ppAssignRhs _  (SetUndefined w) = pure $ text "undef ::" <+> brackets (text (show w))
ppAssignRhs pp (ReadMem a _) = (\d -> text "*" PP.<> d) <$> pp a
ppAssignRhs pp (EvalArchFn f _) = ppArchFn pp f

instance ArchConstraints arch => Pretty (AssignRhs arch ids tp) where
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
collectValueRep _ (AssignedValue a :: Value arch ids tp) = do
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
    docs <- mapM (collectValueRep 0) vals
    return $ brackets $ hcat (punctuate comma docs)

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

instance ( OrdF r
         , ShowF r
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
    -- ^ Write to memory at the given location
   | PlaceHolderStmt !([Some (Value arch ids)]) !String
   | Comment !Text
   | ExecArchStmt (ArchStmt arch ids)
     -- ^ Execute an architecture specific statement

instance ArchConstraints arch => Pretty (Stmt arch ids) where
  pretty (AssignStmt a) = pretty a
  pretty (WriteMem a _ rhs) = text "*" PP.<> prettyPrec 11 a <+> text ":=" <+> ppValue 0 rhs
  pretty (PlaceHolderStmt vals name) = text ("PLACEHOLDER: " ++ name)
                                       <+> parens (hcat $ punctuate comma
                                                   $ map (viewSome (ppValue 0)) vals)
  pretty (Comment s) = text $ "# " ++ Text.unpack s
  pretty (ExecArchStmt s) = prettyF s


instance ArchConstraints arch => Show (Stmt arch ids) where
  show = show . pretty

------------------------------------------------------------------------
-- TermStmt

-- A terminal statement in a block
data TermStmt arch ids
     -- | Fetch and execute the next instruction from the given processor state.
  = FetchAndExecute !(RegState (ArchReg arch) (Value arch ids))
    -- | Branch and execute one block or another.
  | Branch !(Value arch ids BoolType) !(ArchLabel arch) !(ArchLabel arch)
    -- | The syscall instruction.
    -- We model system calls as terminal instructions because from the
    -- application perspective, the semantics will depend on the operating
    -- system.
  | Syscall !(RegState (ArchReg arch) (Value arch ids))
    -- | The block ended prematurely due to an error in instruction
    -- decoding or translation.
    --
    -- This contains the state of the registers when the translation error
    -- occured and the error message recorded.
  | TranslateError !(RegState (ArchReg arch) (Value arch ids)) !Text

instance ( OrdF (ArchReg arch)
         , ShowF (ArchReg arch)
         )
      => Pretty (TermStmt arch ids) where
  pretty (FetchAndExecute s) =
    text "fetch_and_execute" <$$>
    indent 2 (pretty s)
  pretty (Branch c x y) =
    text "branch" <+> ppValue 0 c <+> pretty x <+> pretty y
  pretty (Syscall s) =
    text "syscall" <$$>
    indent 2 (pretty s)
  pretty (TranslateError s msg) =
    text "ERROR: " <+> text (Text.unpack msg) <$$>
    indent 2 (pretty s)

------------------------------------------------------------------------
-- References

-- | Return refernces in a stmt type.
class StmtHasRefs f where
  refsInStmt :: f ids -> Set (Some (AssignId ids))

-- | Return refernces in a function type.
class FnHasRefs (f :: * -> Type -> *) where
  refsInFn  :: f ids tp -> Set (Some (AssignId ids))

refsInValue :: Value arch ids tp -> Set (Some (AssignId ids))
refsInValue (AssignedValue (Assignment v _)) = Set.singleton (Some v)
refsInValue _                                = Set.empty

refsInApp :: App (Value arch ids) tp -> Set (Some (AssignId ids))
refsInApp app = foldApp refsInValue app

refsInAssignRhs :: FnHasRefs (ArchFn arch)
                => AssignRhs arch ids tp
                -> Set (Some (AssignId ids))
refsInAssignRhs rhs =
  case rhs of
    EvalApp v      -> refsInApp v
    SetUndefined _ -> Set.empty
    ReadMem v _    -> refsInValue v
    EvalArchFn f _ -> refsInFn f

------------------------------------------------------------------------
-- Block

-- | A basic block in a control flow graph.
data Block arch ids
   = Block { blockLabel :: !(ArchLabel arch)
           , blockStmts :: !([Stmt arch ids])
             -- ^ List of statements in the block.
           , blockTerm :: !(TermStmt arch ids)
             -- ^ The last statement in the block.
           }

instance ArchConstraints arch => Pretty (Block arch ids) where
  pretty b = do
    pretty (blockLabel b) PP.<> text ":" <$$>
      indent 2 (vcat (pretty <$> blockStmts b) <$$> pretty (blockTerm b))

------------------------------------------------------------------------
-- CFG

-- | A CFG is a map from all reachable code locations
-- to the block for that code location.
data CFG arch ids
   = CFG { _cfgBlocks :: !(Map (ArchLabel arch) (Block arch ids))
         , _cfgBlockRanges :: !(Map (ArchSegmentedAddr arch) (ArchAddr arch))
           -- ^ Maps each address that is the start of a block
           -- to the size of the block.
         }

-- | Create empty CFG
emptyCFG :: CFG addr ids
emptyCFG = CFG { _cfgBlocks = Map.empty
               , _cfgBlockRanges = Map.empty
               }

cfgBlocks :: Simple Lens (CFG arch ids) (Map (ArchLabel arch) (Block arch ids))
cfgBlocks = lens _cfgBlocks (\s v -> s { _cfgBlocks = v })

cfgBlockRanges :: Simple Lens (CFG arch ids) (Map (ArchSegmentedAddr arch) (ArchAddr arch))
cfgBlockRanges = lens _cfgBlockRanges (\s v -> s { _cfgBlockRanges = v })

-- | Return block with given label.
findBlock :: CFG arch ids -> ArchLabel arch -> Maybe (Block arch ids)
findBlock g l = _cfgBlocks g ^. at l

insertBlock :: ( Integral (ArchAddr arch)
               , Ord (ArchAddr arch)
               , Show (ArchAddr arch)
               )
            => Block arch ids
            -> CFG arch ids
            -> CFG arch ids
insertBlock b c = do
  let lbl = blockLabel b
  case findBlock c lbl of
    Just{} -> error $ "Block with label " ++ show (pretty lbl) ++ " already defined."
    Nothing -> c { _cfgBlocks = Map.insert (blockLabel b) b (_cfgBlocks c) }

-- | Inserts blocks for a contiguous region of code.
insertBlocksForCode :: ( Integral (ArchAddr arch)
                       , Show     (ArchAddr arch)
                       )
                    => ArchSegmentedAddr arch -- ^ Start of block
                    -> ArchAddr arch -- ^ Size of block
                    -> [Block arch ids]
                    -> CFG arch ids
                    -> CFG arch ids
insertBlocksForCode start size bs cfg =
  let cfg' = cfg & cfgBlockRanges %~ Map.insert start size
   in foldl' (flip insertBlock) cfg' bs

instance ArchConstraints arch => Pretty (CFG arch ids) where
  pretty g = vcat (pretty <$> Map.elems (_cfgBlocks g))

-- FIXME: refactor to be more efficient
-- FIXME: not a Traversal, more like a map+fold
traverseBlocks :: Ord (ArchAddr arch)
               => CFG arch ids
               -> ArchLabel arch
               -> (Block arch ids -> a)
               -> (a -> a -> a -> a)
               -> a
traverseBlocks cfg root f merge = go root
  where
    go l = case findBlock cfg l of
             Nothing -> error $ "label not found"
             Just b  ->
               let v = f b
                in case blockTerm b of
                     Branch _ lb rb -> merge (go lb) v (go rb)
                     _              -> v

-- | As for traverseBlocks but starting from a block in the cfg, not
-- an address
traverseBlockAndChildren :: Ord (ArchAddr arch)
                         => CFG arch ids
                         -> Block arch ids
                         -> (Block arch ids -> a)
                            -- Maps a block to a value
                         -> (Block arch ids -> a -> a -> a)
                            -- Maps results from to sub-blocks together.
                         -> a
traverseBlockAndChildren cfg b0 f merge = goBlock b0
  where
    goBlock b = case blockTerm b of
                 Branch _ lb rb -> merge b (go lb) (go rb)
                 _              -> f b

    go l = case _cfgBlocks cfg ^. at l of
            Nothing -> error $ "label not found"
            Just b  -> goBlock b
