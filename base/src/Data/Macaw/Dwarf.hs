{- |
Copyright        : (c) Galois, Inc 2018
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines data structures for parsing Dwarf debug information from
binaries.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Dwarf
  ( -- * Compile units and declarations
    dwarfInfoFromElf
  , CompileUnit(..)
  , dwarfGlobals
    -- * Variables
  , Variable(..)
  , InlineVariable(..)
    -- * Sub programs
  , Subprogram(..)
  , SubprogramDef(..)
  , InlinedSubprogram(..)
    -- * Locations
  , Location(..)
  , DeclLoc(..)
    -- * Type information
  , Type(..)
  , TypeF(..)
  , BaseType(..)
  , StructDecl(..)
  , UnionDecl(..)
  , Member(..)
  , EnumDecl(..)
  , Enumerator(..)
  , SubroutineTypeDecl(..)
  , Subrange(..)
  , Typedef(..)
    -- * Exports of "Data.Dwarf"
  , Dwarf.DieID
  , Dwarf.DW_OP(..)
  , Dwarf.Range(..)
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Except
import qualified Control.Monad.Fail as MF
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Binary.Get
import qualified Data.ByteString as BS
import           Data.Dwarf as Dwarf
import qualified Data.ElfEdit as Elf
import           Data.Foldable
import           Data.Int
import           Data.List (partition, sortOn)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

hasAttribute :: DW_AT -> DIE -> Bool
hasAttribute a d = any (\p -> fst p == a) (dieAttributes d)

------------------------------------------------------------------------
-- WarnMonad

-- A monad that allows one to collect warnings with a given type during execution.
class Monad m => WarnMonad s m | m -> s where
  -- Emit the given warning
  warn :: s -> m ()
  -- Run a computation in a context where all warnings are transformed by the given
  -- function.
  runInContext :: (s -> s) -> m r -> m r

instance WarnMonad s m => WarnMonad s (ReaderT r m) where
  warn s = ReaderT $ \_ -> warn s
  runInContext f m = ReaderT $ \r ->
    runInContext f (runReaderT m r)

------------------------------------------------------------------------
-- WarnT

-- | A monad transformer that adds the ability to collect a list of string messages
-- (called "warnings") and throw a string exception.  Fail is overridden
-- to generate
--
-- The warnings are strings,
newtype WarnT m r = WarnT { unWarnT :: ExceptT String (StateT [String] m) r }
  deriving ( Functor, Applicative )

instance Monad m => Monad (WarnT m) where
  m >>= h = WarnT $ unWarnT m >>= unWarnT . h
  return = pure
#if !(MIN_VERSION_base(4,13,0))
  fail = MF.fail
#endif

instance (Monad m) => MF.MonadFail (WarnT m) where
  fail msg = WarnT $ throwError msg

runWarnT :: WarnT m r -> m (Either String r, [String])
runWarnT m = runStateT (runExceptT (unWarnT m)) []

instance Monad m => WarnMonad String (WarnT m) where
  warn msg = WarnT $ ExceptT $ StateT $ \s -> pure (Right (), msg : s)

  runInContext f m = WarnT $ ExceptT $ StateT $ \s -> do
    let g (mr, warnings) = (either (Left . f) Right mr, fmap f warnings ++ s)
     in g <$> runWarnT m

------------------------------------------------------------------------
-- Parser

-- | The context needed to read dwarf entries.
data ParserState = ParserState { expectedPointerWidth :: !Word64
                                 -- ^ Number of bytes a pointer is expected to have.
                               , readerInfo :: !Dwarf.Reader
                               }

newtype Parser r = Parser { unParser :: ReaderT ParserState (WarnT Identity) r }
  deriving ( Functor
           , Applicative
           , Monad
           , WarnMonad String
           , MF.MonadFail
           )


runParser :: Word64 -> Dwarf.Reader -> Parser r -> (Either String r, [String])
runParser w dr p = runIdentity (runWarnT (runReaderT (unParser p) s))
  where s = ParserState { expectedPointerWidth = w
                        , readerInfo = dr
                        }

------------------------------------------------------------------------
-- Parser functions

convertAttribute :: DW_AT
                 -> (DW_ATVAL -> Parser r)
                 -> DW_ATVAL -> Parser r
convertAttribute dat f v = runInContext h (f v)
  where h msg = "Could not interpret attribute " ++ show dat ++ " value " ++ show v ++ ": " ++ msg

attributeAsBlob :: DW_ATVAL -> Parser BS.ByteString
attributeAsBlob (DW_ATVAL_BLOB b) = pure b
attributeAsBlob _ = fail "Could not interpret as BLOB"

attributeAsBool :: DW_ATVAL -> Parser Bool
attributeAsBool (DW_ATVAL_BOOL b) = pure b
attributeAsBool _ = fail "Could not interpret as Bool"

attributeAsInt :: DW_ATVAL -> Parser Int64
attributeAsInt (DW_ATVAL_INT u) = pure u
attributeAsInt _ = fail "Could not interpret as Int"

attributeAsUInt :: DW_ATVAL -> Parser Word64
attributeAsUInt (DW_ATVAL_UINT u) = pure u
attributeAsUInt _ = fail "Could not interpret as UInt"

-- | Parse an attribute as a DIE identifier.
attributeAsDieID :: DW_ATVAL -> Parser DieID
attributeAsDieID (DW_ATVAL_REF r) = pure r
attributeAsDieID _ = fail "Could not interpret as DieID."

attributeAsString :: DW_ATVAL -> Parser String
attributeAsString (DW_ATVAL_STRING s) = pure s
attributeAsString _ = fail "Could not interpret as string."

lookupDIE :: Map DieID v -> DieID -> Parser v
lookupDIE m k =
  case Map.lookup k m of
    Just d -> pure d -- (dieRefsDIE d)
    Nothing -> fail $ "Could not find " ++ show k

resolveDieIDAttribute :: Map DieID v -> DW_ATVAL -> Parser v
resolveDieIDAttribute m v = lookupDIE m =<< attributeAsDieID v

attributeAsLang :: DW_ATVAL -> Parser DW_LANG
attributeAsLang v = DW_LANG <$> attributeAsUInt v

parseGet :: BS.ByteString -> Get a -> Parser a
parseGet bs m =
  case pushEndOfInput (runGetIncremental m `pushChunk` bs) of
    Fail _ _ msg -> fail msg
    Partial _ -> fail "Unexpected partial"
    Done _ _ r -> do
      pure r

attributeAsFilename :: V.Vector FilePath -> DW_ATVAL -> Parser FilePath
attributeAsFilename v val = do
  idx <- attributeAsUInt val
  if idx == 0 then
    pure ""
   else
    case v V.!? fromIntegral (idx - 1) of
      Just e -> pure e
      Nothing -> fail $ "Could not match filename index " ++ show idx ++ "."

------------------------------------------------------------------------
-- Range

ppRange :: Range -> Doc
ppRange (Range x y) =
    text "low:" <+> text (showHex x "") <+> text "high:" <+> text (showHex y "")

------------------------------------------------------------------------
-- DIEParser

data DIEParserState = DPS { dpsDIE :: DIE
                          , dpsAttributeMap :: Map DW_AT [DW_ATVAL]
                            -- ^ Maps attributes to the set of values with that attribute.
                          , _dpsSeenAttributes :: Set DW_AT
                            -- ^ Set of attributes that a parser has searched for.
                            --
                            -- Used so that we can flag when a DIE contains an attribute
                            -- we have not considered.
                          , dpsChildrenMap     :: Map DW_TAG [DIE]
                            -- ^ Maps tags to the set of child die nodes with that tag.
                          , _dpsSeenChildren   :: Set DW_TAG
                            -- ^ Set of tags for children that we have attempted to
                            -- parse.
                            --
                            -- Used so that we can flag when a DIE contains a child tag
                            -- we have not considered.
                          }

dpsSeenAttributes :: Lens' DIEParserState (Set DW_AT)
dpsSeenAttributes = lens _dpsSeenAttributes (\s v -> s { _dpsSeenAttributes = v })

dpsSeenChildren :: Lens' DIEParserState (Set DW_TAG)
dpsSeenChildren = lens _dpsSeenChildren (\s v -> s { _dpsSeenChildren = v })

type DIEParser = StateT DIEParserState Parser

taggedError :: String -> String -> String
taggedError nm msg =
  "Error parsing " ++ nm ++ ":\n" ++ unlines (("  " ++) <$> lines msg)

runDIEParser :: String -> DIE -> DIEParser r -> Parser r
runDIEParser ctx d act = runInContext (taggedError (ctx ++ " " ++ show (dieId d) ++ " " ++ show (dieTag d))) $ do
  let childMap :: Map DW_TAG [DIE]
      childMap = foldr' (\d' -> Map.insertWith (++) (dieTag d') [d']) Map.empty (dieChildren d)
      attrMap  = foldr' (\(k,v) -> Map.insertWith (++) k [v])     Map.empty (dieAttributes d)
      s0 = DPS { dpsDIE = d
               , dpsAttributeMap = attrMap
               , _dpsSeenAttributes = Set.empty
               , dpsChildrenMap = childMap
               , _dpsSeenChildren = Set.empty
               }
  (r, s1) <- runStateT act s0
  do let missingTags = Map.keysSet childMap `Set.difference` (s1^.dpsSeenChildren)
     when (not (Set.null missingTags)) $ do
       forM_ (dieChildren d) $ \child -> do
         when (not (Set.member (dieTag child) (s1^.dpsSeenChildren))) $ do
           warn $ "Unexpected child for " ++ ctx ++ ": " ++ show child
  do let missingAttrs = Map.keysSet attrMap `Set.difference` (s1^.dpsSeenAttributes)
     when (not (Set.null missingAttrs)) $ do
       warn $ "Unexpected attributes: " ++ show (Set.toList missingAttrs) ++ "\n" ++ show d
  pure r

checkTag :: DW_TAG -> DIEParser ()
checkTag tag = do
  d <- gets dpsDIE
  lift $ when (dieTag d /= tag) $ warn ("Expected " ++ show tag)

ignoreAttribute :: DW_AT -> DIEParser ()
ignoreAttribute dat = do
  dpsSeenAttributes %= Set.insert dat

ignoreChild :: DW_TAG -> DIEParser ()
ignoreChild dat = do
  dpsSeenChildren %= Set.insert dat

getSingleAttribute :: DW_AT -> (DW_ATVAL -> Parser v) -> DIEParser v
getSingleAttribute dat f = do
  d <- gets dpsDIE
  m <- gets dpsAttributeMap
  case fromMaybe [] (Map.lookup dat m) of
    [] -> fail $ "Expected attribute " ++ show dat ++ " in " ++ show d ++ "."
    [v] -> do
      ignoreAttribute dat
      lift $ convertAttribute dat f v
    _ -> fail $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

getMaybeAttribute :: DW_AT -> (DW_ATVAL -> Parser v) -> DIEParser (Maybe v)
getMaybeAttribute dat f = do
  d <- gets dpsDIE
  m <- gets dpsAttributeMap
  case fromMaybe [] (Map.lookup dat m) of
    [] -> do
      ignoreAttribute dat
      pure Nothing
    [v] -> do
      ignoreAttribute dat
      lift $ Just <$> convertAttribute dat f v
    _ -> fail $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

parseChildrenList :: DW_TAG -> (DIE -> Parser v) -> DIEParser [v]
parseChildrenList tag f = do
  ignoreChild tag
  m <- gets dpsChildrenMap
  lift $ traverse f $ fromMaybe [] $ Map.lookup tag m

------------------------------------------------------------------------
-- DeclLoc

-- | A file and line number for a declaration.
data DeclLoc = DeclLoc { locFile :: !FilePath
                       , locLine :: !Word64
                       }

instance Pretty DeclLoc where
  pretty loc =
    text "decl_file:  " <+> text (locFile loc) <$$>
    text "decl_line:  " <+> text (show (locLine loc))

instance Show DeclLoc where
  show = show . pretty

-- | Read the decl_file and decl_line attributes from the DIE
parseDeclLoc :: V.Vector FilePath -> DIEParser DeclLoc
parseDeclLoc file_vec = do
  declFile   <- getSingleAttribute DW_AT_decl_file  (attributeAsFilename file_vec)
  declLine   <- getSingleAttribute DW_AT_decl_line  attributeAsUInt
  pure $! DeclLoc { locFile = declFile
                  , locLine = declLine
                  }

------------------------------------------------------------------------
-- DW_OP operations

ppOp :: DW_OP -> Doc
ppOp (DW_OP_addr w) | w >= 0 = text (showHex w "")
ppOp o = text (show o)

ppOps :: [DW_OP] -> Doc
ppOps l = hsep (ppOp <$> l)

parseDwarfExpr :: BS.ByteString -> Parser [DW_OP]
parseDwarfExpr bs = do
  dr <- Parser $ asks readerInfo
  parseGet bs (getWhileNotEmpty (getDW_OP dr))

------------------------------------------------------------------------
-- Enumerator

data Enumerator = Enumerator { enumName :: !String
                             , enumValue :: Int64
                             }
  deriving (Show)

parseEnumerator :: DIE -> Parser Enumerator
parseEnumerator d = runDIEParser "parseEnumerator" d $ do
  checkTag DW_TAG_enumerator
  name       <- getSingleAttribute DW_AT_name        attributeAsString
  val        <- getSingleAttribute DW_AT_const_value attributeAsInt
  pure Enumerator { enumName = name
                  , enumValue = val
                  }

------------------------------------------------------------------------
-- Subrange

data Subrange tp = Subrange { subrangeType :: tp
                            , subrangeUpperBound :: [DW_OP]
                            }
  deriving (Show)


subrangeTypeLens :: Lens (Subrange a) (Subrange b) a b
subrangeTypeLens = lens subrangeType (\s v -> s { subrangeType = v })

getWhileNotEmpty :: Get a -> Get [a]
getWhileNotEmpty act = go []
  where go prev = do
          e <- isEmpty
          if e then
            pure (reverse prev)
           else do
            v <- act
            go $! v : prev

parseSubrange :: DIE -> Parser (Subrange DieID)
parseSubrange d = runDIEParser "parseSubrange" d $ do
  dr <- lift $ Parser $ asks readerInfo
  tp    <- getSingleAttribute DW_AT_type attributeAsDieID
  upper <- getSingleAttribute DW_AT_upper_bound $ \case
    DW_ATVAL_UINT w ->
      pure [DW_OP_const8u w]
    DW_ATVAL_BLOB bs -> do
      parseGet bs (getWhileNotEmpty (getDW_OP dr))
    _ -> fail "Invalid upper bound"

  pure Subrange { subrangeType = tp
                , subrangeUpperBound = upper
                }

------------------------------------------------------------------------
-- Type

data BaseType = BaseTypeDef { baseSize     :: !Word64
                            , baseEncoding :: !DW_ATE
                            , baseName     :: !String
                            }
  deriving (Show)

data Member tp = Member { memberName :: !String
                        , memberDeclLoc  :: !(Maybe DeclLoc)
                        , memberLoc      :: !(Maybe Word64)
                        , memberType     :: tp
                        }
  deriving (Show)

data StructDecl tp = StructDecl { structName     :: !String
                                , structByteSize :: !Word64
                                , structLoc      :: !DeclLoc
                                , structMembers  :: ![Member tp]
                                }
  deriving (Show)

data UnionDecl tp = UnionDecl { unionName     :: !String
                              , unionByteSize :: !Word64
                              , unionLoc      :: !DeclLoc
                              , unionMembers  :: ![Member tp]
                              }
  deriving (Show)

data EnumDecl = EnumDecl { enumDeclName :: Maybe String
                         , enumDeclByteSize :: !Word64
                         , enumDeclLoc      :: !DeclLoc
                         , enumDeclCases    :: ![Enumerator]
                         }
  deriving (Show)

data SubroutineTypeDecl tp
   = SubroutineTypeDecl { fntypePrototyped :: !(Maybe Bool)
                        , fntypeFormals    :: ![DIE]
                        , fntypeType       :: !(Maybe tp)
                        }
  deriving (Show)

data Typedef tp = Typedef { typedefName :: !String
                          , typedefLoc  :: !DeclLoc
                          , typedefType :: tp
                          }
  deriving (Show)



data TypeF tp
   = BoolType
     -- ^ A 1-byte boolean value (0 is false, nonzero is true)
   | UnsignedIntType !Int
     -- ^ An unsigned integer with the given number of bytes (should be positive)
     -- The byte order is platform defined.
   | SignedIntType !Int
     -- ^ An signed integer with the given number of bytes (should be positive)
     -- The byte order is platform defined.
   | FloatType
     -- ^ An IEEE single precision floating point value.
   | DoubleType
     -- ^ An IEEE double precision floating point value.
   | UnsignedCharType
     -- ^ A 1-byte unsigned character.
   | SignedCharType
     -- ^ A 1-byte signed character.

   | ArrayType tp ![Subrange tp]
   | PointerType !(Maybe tp)
     -- ^ A pointer with the given type (or 'Nothing') to indicate this is a void pointer.
   | StructType !(StructDecl tp)
     -- ^ Denotes a C struct
   | UnionType !(UnionDecl tp)
     -- ^ Denotes a C union
   | EnumType !EnumDecl
   | SubroutinePtrType !(SubroutineTypeDecl tp)
   | TypedefType !(Typedef tp)
  deriving (Show)

structMembersLens :: Lens (StructDecl a) (StructDecl b) [Member a] [Member b]
structMembersLens = lens structMembers (\s v -> s { structMembers = v })

unionMembersLens :: Lens (UnionDecl a) (UnionDecl b) [Member a] [Member b]
unionMembersLens = lens unionMembers (\s v -> s { unionMembers = v })

memberTypeLens :: Lens (Member a) (Member b) a b
memberTypeLens = lens memberType (\s v -> s { memberType = v })

subroutineTypeLens :: Lens (SubroutineTypeDecl a) (SubroutineTypeDecl b) (Maybe a) (Maybe b)
subroutineTypeLens = lens fntypeType (\s v -> s { fntypeType = v })

typedefTypeLens :: Lens (Typedef a) (Typedef b) a b
typedefTypeLens = lens typedefType (\s v -> s { typedefType = v })

traverseSubtypes :: Traversal (TypeF a) (TypeF b) a b
traverseSubtypes f tf =
  case tf of
    BoolType          -> pure BoolType
    UnsignedIntType w -> pure (UnsignedIntType w)
    SignedIntType w   -> pure (SignedIntType w)
    FloatType         -> pure FloatType
    DoubleType        -> pure DoubleType
    UnsignedCharType  -> pure UnsignedCharType
    SignedCharType    -> pure SignedCharType
    ArrayType etp d -> ArrayType <$> f etp <*> (traverse . subrangeTypeLens) f d
    PointerType tp -> PointerType <$> traverse f tp
    StructType s -> StructType <$> (structMembersLens . traverse . memberTypeLens) f s
    UnionType  u -> UnionType  <$> (unionMembersLens . traverse . memberTypeLens) f u
    EnumType e -> pure (EnumType e)
    SubroutinePtrType d -> SubroutinePtrType <$> (subroutineTypeLens . traverse) f d
    TypedefType tp -> TypedefType <$> typedefTypeLens f tp

parseMember :: V.Vector FilePath -> DIE -> Parser (Member DieID)
parseMember file_vec d = runDIEParser "parseMember" d $ do
  checkTag DW_TAG_member
  name       <- getSingleAttribute DW_AT_name       attributeAsString
  tp         <- getSingleAttribute DW_AT_type attributeAsDieID
  memLoc     <- getMaybeAttribute  DW_AT_data_member_location  attributeAsUInt
  artificial <- fromMaybe False <$> getMaybeAttribute DW_AT_artificial attributeAsBool
  mdloc <-
    if artificial then
      pure Nothing
     else
      Just <$> parseDeclLoc file_vec

  pure $! Member { memberName = name
                 , memberDeclLoc  = mdloc
                 , memberLoc = memLoc
                 , memberType = tp
                 }

attributeAsBaseTypeEncoding :: DW_ATVAL -> Parser DW_ATE
attributeAsBaseTypeEncoding v = do
  u <- attributeAsUInt v
  case get_dw_ate u of
    Just r -> pure r
    Nothing -> fail $ "Could not parser attribute encoding 0x" ++ showHex u "."

data PreType
   = PreTypeF !(TypeF DieID)
   | EmptyConst
     -- ^ Denotes an const die with no attributes
   | ConstTypeF !DieID
     -- ^ A const value with the given die ID.
   | VolatileTypeF !DieID
   | SubroutineTypeF !(SubroutineTypeDecl DieID)

-- | A type parser takes the file vector and returns either a `TypeF` or `Nothing`.
--
-- The nothing value is returned, because `DW_TAG_const_type` with no `DW_AT_type`
-- attribute.
type TypeParser = V.Vector FilePath -> DIEParser PreType

parseBaseType :: TypeParser
parseBaseType _ = do
  name <- getSingleAttribute DW_AT_name      attributeAsString
  enc  <- getSingleAttribute DW_AT_encoding  attributeAsBaseTypeEncoding
  size <- getSingleAttribute DW_AT_byte_size attributeAsUInt
  case (name, enc,size) of
    (_, DW_ATE_boolean, 1) -> pure $ PreTypeF BoolType

    (_, DW_ATE_signed,   _) | size >= 1 -> pure $ PreTypeF $ SignedIntType (fromIntegral size)
    (_, DW_ATE_unsigned, _) | size >= 1 -> pure $ PreTypeF $ UnsignedIntType (fromIntegral size)

    (_, DW_ATE_float,    4) -> pure $ PreTypeF $ FloatType
    (_, DW_ATE_float,    8) -> pure $ PreTypeF $ DoubleType

    (_, DW_ATE_signed_char, 1)   -> pure $ PreTypeF $ SignedCharType
    (_, DW_ATE_unsigned_char, 1) -> pure $ PreTypeF $ UnsignedCharType
    _ -> fail ("Unsupported base type " ++ show name ++ " " ++ show enc ++ " " ++ show size)

parseConstType :: TypeParser
parseConstType _ = do
  ma <- getMaybeAttribute DW_AT_type attributeAsDieID
  case ma of
    Just a  -> pure $ ConstTypeF a
    Nothing -> pure $ EmptyConst


parseVolatileType :: TypeParser
parseVolatileType _ = do
  VolatileTypeF <$> getSingleAttribute DW_AT_type attributeAsDieID

parsePointerType :: TypeParser
parsePointerType _ = do
  expected <- lift $ Parser $ asks expectedPointerWidth
  mtp <- getMaybeAttribute DW_AT_type attributeAsDieID
  w <- getSingleAttribute DW_AT_byte_size attributeAsUInt
  when (w /= expected) $ do
    fail $ "Found pointer width of " ++ show w ++ " when " ++ show expected ++ " expected."
  pure $ PreTypeF $ PointerType mtp

parseStructureType :: TypeParser
parseStructureType file_vec = do
  name       <- fromMaybe "" <$> getMaybeAttribute DW_AT_name       attributeAsString
  byte_size  <- getSingleAttribute DW_AT_byte_size  attributeAsUInt
  declLoc    <- parseDeclLoc file_vec
  ignoreAttribute DW_AT_sibling

  members <- parseChildrenList DW_TAG_member (parseMember file_vec)

  let struct = StructDecl { structName     = name
                          , structByteSize = byte_size
                          , structLoc      = declLoc
                          , structMembers  = members
                          }
  pure $ PreTypeF $ StructType struct

parseUnionType :: TypeParser
parseUnionType file_vec = do
  name       <- fromMaybe "" <$> getMaybeAttribute DW_AT_name       attributeAsString
  byte_size  <- getSingleAttribute DW_AT_byte_size  attributeAsUInt
  declLoc    <- parseDeclLoc file_vec
  ignoreAttribute DW_AT_sibling

  members <- parseChildrenList DW_TAG_member (parseMember file_vec)

  let u = UnionDecl { unionName     = name
                    , unionByteSize = byte_size
                    , unionLoc      = declLoc
                    , unionMembers  = members
                    }
  pure $ PreTypeF $ UnionType u

parseTypedefType :: TypeParser
parseTypedefType file_vec = do
  name       <- getSingleAttribute DW_AT_name       attributeAsString
  declLoc    <- parseDeclLoc file_vec
  tp <- getSingleAttribute DW_AT_type attributeAsDieID

  let td = Typedef { typedefName = name
                   , typedefLoc  = declLoc
                   , typedefType = tp
                   }
  pure $ PreTypeF $ TypedefType td

parseArrayType :: TypeParser
parseArrayType _ = do
  eltType <- getSingleAttribute DW_AT_type attributeAsDieID
  ignoreAttribute DW_AT_sibling
  sr <- parseChildrenList DW_TAG_subrange_type parseSubrange
  pure $ PreTypeF $ ArrayType eltType sr

parseEnumerationType :: TypeParser
parseEnumerationType file_vec = do
  mname      <- getMaybeAttribute  DW_AT_name       attributeAsString
  byte_size  <- getSingleAttribute DW_AT_byte_size  attributeAsUInt
  declLoc    <- parseDeclLoc file_vec
  ignoreAttribute DW_AT_sibling

  cases <- parseChildrenList DW_TAG_enumerator parseEnumerator
  let e = EnumDecl { enumDeclName     = mname
                   , enumDeclByteSize = byte_size
                   , enumDeclLoc      = declLoc
                   , enumDeclCases    = cases
                   }
  pure $ PreTypeF $ EnumType e

-- | Parse a subroutine type.
parseSubroutineType :: TypeParser
parseSubroutineType _ = do
  proto <- getMaybeAttribute DW_AT_prototyped attributeAsBool
  ignoreAttribute DW_AT_sibling
  formals <- parseChildrenList DW_TAG_formal_parameter pure

  tp <- getMaybeAttribute DW_AT_type attributeAsDieID

  let sub = SubroutineTypeDecl { fntypePrototyped = proto
                               , fntypeFormals    = formals
                               , fntypeType       = tp
                               }
  pure $ SubroutineTypeF sub

typeParsers :: Map DW_TAG TypeParser
typeParsers = Map.fromList
  [ (,) DW_TAG_base_type        parseBaseType
  , (,) DW_TAG_const_type       parseConstType
  , (,) DW_TAG_volatile_type    parseVolatileType
  , (,) DW_TAG_pointer_type     parsePointerType
  , (,) DW_TAG_structure_type   parseStructureType
  , (,) DW_TAG_union_type       parseUnionType
  , (,) DW_TAG_typedef          parseTypedefType
  , (,) DW_TAG_array_type       parseArrayType
  , (,) DW_TAG_enumeration_type parseEnumerationType
  , (,) DW_TAG_subroutine_type  parseSubroutineType
  ]

-- | Parse a type given a vector identifying file vectors.
parseTypeMap :: V.Vector FilePath -> DIEParser (Map DieID Type)
parseTypeMap file_vec = do
  let go :: (DW_TAG, TypeParser) -> DIEParser [(DieID, PreType)]
      go (tag, act) = do
        parseChildrenList tag $ \d ->
          (\tf -> (dieId d, tf)) <$> runDIEParser "parseTypeF" d (act file_vec)
  resolveTypeMap . concat <$> traverse go (Map.toList typeParsers)

------------------------------------------------------------------------
-- Type

-- | A type in the Dwarf file as represented by a recursive application
-- of 'TypeF'.
data Type = Type { typeF :: !(TypeF Type)
                 , typeIsConst :: !Bool
                 , typeIsVolatile :: !Bool
                 }

instance Show Type where
  show = show . ppType

ppTypeF :: TypeF Type -> Doc
ppTypeF tp =
  case tp of
    BoolType            -> text "bool"
    UnsignedIntType w   -> text "unsignedt<" <> text (show (8*w)) <> ">"
    SignedIntType w     -> text "signed<"    <> text (show (8*w)) <> ">"
    FloatType           -> text "float"
    DoubleType          -> text "double"
    UnsignedCharType    -> text "uchar"
    SignedCharType      -> text "schar"
    PointerType x       -> text "pointer" <+> maybe (text "unknown") ppType x
    StructType s        -> text "struct"  <+> text (structName s)
    UnionType  u        -> text "union"   <+> text (unionName  u)
    EnumType e          -> text "enum"        <+> text (show e)
    TypedefType d       -> text "typedef"     <+> text (typedefName d)
    ArrayType etp l     -> text "array"       <+> ppType etp <+> text (show l)
    SubroutinePtrType d -> text "subroutine*" <+> text (show d)

ppType :: Type -> Doc
ppType tp =  (if typeIsConst tp then text "const " else empty)
          <> (if typeIsVolatile tp then text "volatile " else empty)
          <> ppTypeF (typeF tp)

-- | Resolve pretype to map from die identifiers to type.
resolveTypeMap :: [(DieID, PreType)] -> Map DieID Type
resolveTypeMap m = r
  where premap :: Map DieID PreType
        premap = Map.fromList m
        r = Map.fromAscList
          [ (d, tp)
          | (d, tf) <- Map.toAscList premap
          , Just tp <- [resolve tf]
          ]

        resolve :: PreType -> Maybe Type
        resolve (PreTypeF (PointerType (Just d)))
          | Just (SubroutineTypeF decl) <- Map.lookup d premap =
              Just $ Type { typeF = SubroutinePtrType (decl & subroutineTypeLens . traverse %~ g)
                          , typeIsConst = False
                          , typeIsVolatile = False
                          }

        resolve (PreTypeF tf) = Just $ Type { typeF = tf & traverseSubtypes %~ g
                                            , typeIsConst = False
                                            , typeIsVolatile = False
                                            }
        resolve EmptyConst = Nothing
        resolve (ConstTypeF d) = Just $ (g d) { typeIsConst = True }
        resolve (VolatileTypeF d) = Just $ (g d) { typeIsVolatile = True }
        resolve (SubroutineTypeF _) = Nothing

        g :: DieID -> Type
        g d = fromMaybe (error $ "Could not find die ID " ++ show d) $
              Map.lookup d r

------------------------------------------------------------------------
-- Variable

-- | Provides a way of computing the location of a variable.
data Location
   = ComputedLoc [DW_OP]
   | OffsetLoc Word64
  deriving (Eq, Ord)

instance Pretty Location where
  pretty (ComputedLoc ops) = ppOps ops
  pretty (OffsetLoc w) = text ("offset 0x" ++ showHex w "")

data Variable = Variable { varDieID    :: !DieID
                         , varName     :: !String
                         , varDecl     :: !Bool
                           -- ^ Indicates if this variable is just a declaration
                         , varDeclLoc  :: !DeclLoc
                         , varType     :: !Type
                         , varLocation :: !(Maybe Location)
                         }

instance Pretty Variable where
  pretty v =
    text "name:    " <+> text (varName v) <$$>
    pretty (varDeclLoc v) <$$>
    text "type:    " <+> ppType (varType v) <$$>
    maybe (text "") (\l -> text "location:" <+> pretty l) (varLocation v)

instance Show Variable where
   show = show . pretty

parseType :: Map DieID tp -> DieID -> Parser tp
parseType m k =
  case Map.lookup k m of
    Just v -> pure v
    Nothing -> fail $ "Could not resolve type with id " ++ show k ++ "."

data ConstValue
  = ConstBlob BS.ByteString
  | ConstInt  Int64
  | ConstUInt Word64

parseVariable :: V.Vector FilePath
              -> Map DieID Type
              -> DIE
              -> Parser Variable
parseVariable = parseVariableOrParameter DW_TAG_variable

parseParameter :: V.Vector FilePath
               -> Map DieID Type
               -> DIE
               -> Parser Variable
parseParameter = parseVariableOrParameter DW_TAG_formal_parameter

parseVariableOrParameter :: Dwarf.DW_TAG
                         -> V.Vector FilePath
                         -> Map DieID Type
                         -> DIE
                         -> Parser Variable
parseVariableOrParameter tag file_vec typeMap d = runDIEParser "parseVariable" d $ do
  checkTag tag

  mloc       <- getMaybeAttribute DW_AT_location $ \case
                  DW_ATVAL_BLOB b -> ComputedLoc <$> parseDwarfExpr b
                  DW_ATVAL_UINT w -> pure (OffsetLoc w)
                  _ -> fail $ "Could not interpret location"

  name       <- getSingleAttribute DW_AT_name       attributeAsString
  declLoc    <- parseDeclLoc file_vec
  var_type   <- getSingleAttribute DW_AT_type $
                      parseType typeMap <=< attributeAsDieID

  _cv   <- getMaybeAttribute DW_AT_const_value $ \case
             DW_ATVAL_BLOB bs -> pure $! ConstBlob bs
             DW_ATVAL_INT  w  -> pure $! ConstInt  w
             DW_ATVAL_UINT w  -> pure $! ConstUInt w
             _ -> fail $ "Could not interpret const value."
  decl <- fmap (fromMaybe False) $ getMaybeAttribute DW_AT_declaration $ attributeAsBool
  _exte <- getMaybeAttribute DW_AT_external    $ attributeAsBool

  pure $! Variable { varDieID    = dieId d
                   , varName     = name
                   , varDecl     = decl
                   , varDeclLoc  = declLoc
                   , varType     = var_type
                   , varLocation = mloc
                   }

data InlineVariable = InlineVariable { ivarOrigin :: Variable
                                     , ivarLoc    :: !(Maybe Location)
                                     }

attributeAsLocation :: DW_ATVAL -> Parser Location
attributeAsLocation = \case
  DW_ATVAL_BLOB b -> ComputedLoc <$> parseDwarfExpr b
  DW_ATVAL_UINT w -> pure (OffsetLoc w)
  _ -> fail $ "Could not interpret location"

parseInlineVariable :: Map DieID Variable
                    -> DIE
                    -> Parser InlineVariable
parseInlineVariable varMap d = runDIEParser "parseInlineVariable" d $ do
  checkTag DW_TAG_variable

  origin <- getSingleAttribute DW_AT_abstract_origin (resolveDieIDAttribute varMap)
  mloc       <- getMaybeAttribute DW_AT_location attributeAsLocation

  pure $! InlineVariable { ivarOrigin = origin
                         , ivarLoc    = mloc
                         }

------------------------------------------------------------------------
-- Subprogram


data SubprogramDef = SubprogramDef { subRange  :: !Dwarf.Range
                                   , subFrameBase  :: ![DW_OP]
                                   , subGNUAllCallSites :: !(Maybe Bool)
                                   }

instance Pretty SubprogramDef where
  pretty d =
     vcat [ text "low_pc:     " <+> text (showHex l "")
          , text "high_pc:    " <+> text (showHex h "")
          , text "frame_base: " <+> text (show (subFrameBase d))
          , text "GNU_all_call_sites: " <+> text (show (subGNUAllCallSites d))
          ]
    where Range l h = subRange d

parseSubprogramDef :: V.Vector FilePath
                   -> Map DieID Type
                   -> DIEParser SubprogramDef
parseSubprogramDef _ _ = do
  lowPC      <- getSingleAttribute DW_AT_low_pc     attributeAsUInt
  highPC     <- getSingleAttribute DW_AT_high_pc    attributeAsUInt
  frameBase  <- getSingleAttribute DW_AT_frame_base $
                  parseDwarfExpr <=< attributeAsBlob
  callSites  <- getMaybeAttribute  DW_AT_GNU_all_call_sites attributeAsBool
  ignoreChild DW_TAG_formal_parameter
  ignoreChild DW_TAG_lexical_block
  ignoreChild DW_TAG_GNU_call_site
  ignoreChild DW_TAG_inlined_subroutine
  pure $ SubprogramDef { subRange     = Range lowPC (lowPC + highPC)
                       , subFrameBase = frameBase
                       , subGNUAllCallSites = callSites
                       }

data Subprogram = Subprogram { subExternal   :: !Bool
                             , subName       :: !String
                             , subDeclLoc    :: !(Maybe DeclLoc)
                             , subPrototyped :: !Bool
                             , subDef        :: !(Maybe SubprogramDef)
                             , subVars :: !(Map DieID Variable)
                             , subParams :: !(Map DieID Variable)
                             , subRetType :: !(Maybe Type)
                             }



instance Pretty Subprogram where
  pretty sub =
    vcat [ text "external:   " <+> text (show (subExternal sub))
         , text "name:       " <+> text (subName sub)
         , maybe (text "") pretty (subDeclLoc sub)
         , text "prototyped: " <+> text (show (subPrototyped sub))
         , maybe (text "") pretty (subDef sub)
         , ppList "variables" (pretty <$> Map.elems (subVars sub))
         , ppList "parameters" (pretty <$> Map.elems (subParams sub))
         , text "return type: " <+> text (show (subRetType sub))
         ]

instance Show Subprogram where
  show = show . pretty

parseSubprogram :: V.Vector FilePath
                -> Map DieID Type
                -> DIE
                -> Parser Subprogram
parseSubprogram file_vec typeMap d = runDIEParser "parseSubprogram" d $ do
  checkTag DW_TAG_subprogram

  ext        <- fromMaybe False <$> getMaybeAttribute DW_AT_external   attributeAsBool

  decl       <- fromMaybe False <$> getMaybeAttribute DW_AT_declaration attributeAsBool
  inl        <- fromMaybe DW_INL_not_inlined <$>
    getMaybeAttribute DW_AT_inline (\v -> dw_inl <$> attributeAsUInt v)
  let inlined = case inl of
                  DW_INL_not_inlined          -> False
                  DW_INL_inlined              -> True
                  DW_INL_declared_not_inlined -> False
                  DW_INL_declared_inlined     -> True
  def <-
    if decl || inlined then
      pure Nothing
     else do
      Just <$> parseSubprogramDef file_vec typeMap

  name       <- getSingleAttribute DW_AT_name       attributeAsString
  prototyped <- getMaybeAttribute DW_AT_prototyped attributeAsBool
  artificial <- fromMaybe False <$> getMaybeAttribute DW_AT_artificial attributeAsBool
  mloc <-
    if artificial then
      pure Nothing
     else
      Just <$> parseDeclLoc file_vec

  typeMap' <- Map.union typeMap <$> parseTypeMap file_vec

  vars <- parseChildrenList DW_TAG_variable (parseVariable file_vec typeMap')
  params <- parseChildrenList DW_TAG_formal_parameter $
    parseParameter file_vec typeMap'
  retType <- getMaybeAttribute DW_AT_type $
    parseType typeMap' <=< attributeAsDieID

  ignoreAttribute DW_AT_GNU_all_tail_call_sites
  ignoreAttribute DW_AT_sibling
  ignoreAttribute DW_AT_type

  ignoreChild DW_TAG_formal_parameter
  ignoreChild DW_TAG_label
  ignoreChild DW_TAG_lexical_block
  ignoreChild DW_TAG_unspecified_parameters

  pure Subprogram { subExternal   = ext
                  , subName       = name
                  , subDeclLoc    = mloc
                  , subPrototyped = fromMaybe False prototyped
                  , subDef        = def
                  , subVars       = Map.fromList [ (varDieID v, v) | v <- vars ]
                  , subParams     = Map.fromList [ (varDieID p, p) | p <- params ]
                  , subRetType    = retType
                  }

------------------------------------------------------------------------
-- Inlined Subprogram

data InlinedSubprogram = InlinedSubprogram { isubExternal   :: !Bool
                                           , isubOrigin     :: !Subprogram
                                           , isubDef        :: !(Maybe SubprogramDef)
                                           , isubVars       :: ![InlineVariable]
                                           }

instance Pretty InlinedSubprogram where
  pretty sub =
    text "external:   " <+> text (show (isubExternal sub)) <$$>
    text "origin:" <$$>
    indent 2 (pretty (isubOrigin sub)) <$$>
    maybe (text "") pretty (isubDef sub)

parseInlinedSubprogram :: V.Vector FilePath
                       -> Map DieID Type
                       -> Map DieID Subprogram
                       -> DIE
                       -> Parser InlinedSubprogram
parseInlinedSubprogram file_vec typeMap subprogramMap d =
 runDIEParser "parseInlinedSubprogram" d $ do
  checkTag DW_TAG_subprogram
  ext        <- fromMaybe False <$> getMaybeAttribute DW_AT_external   attributeAsBool

  decl       <- fromMaybe False <$> getMaybeAttribute DW_AT_declaration attributeAsBool
  inl        <- fromMaybe DW_INL_not_inlined <$>
    getMaybeAttribute DW_AT_inline (\v -> dw_inl <$> attributeAsUInt v)
  let inlined = case inl of
                  DW_INL_not_inlined          -> False
                  DW_INL_inlined              -> True
                  DW_INL_declared_not_inlined -> False
                  DW_INL_declared_inlined     -> True
  origin <- getSingleAttribute DW_AT_abstract_origin (resolveDieIDAttribute subprogramMap)

  def <-
    if decl || inlined then
      pure Nothing
     else do
      Just <$> parseSubprogramDef file_vec typeMap


  let varMap = subVars origin
  ivars <- parseChildrenList DW_TAG_variable (parseInlineVariable varMap)

  ignoreAttribute DW_AT_sibling

  pure InlinedSubprogram
        { isubExternal   = ext
        , isubOrigin     = origin
        , isubDef        = def
        , isubVars       = ivars
        }

------------------------------------------------------------------------
-- CompileUnit

-- | The output of one compilation.
data CompileUnit = CompileUnit { cuProducer    :: String
                               , cuLanguage    :: Maybe DW_LANG
                               , cuName        :: String
                               , cuCompDir     :: String
                               , cuGNUMacros   :: !(Maybe Word64)
                               , cuSubprograms :: ![Subprogram]
                               , cuInlinedSubprograms :: ![InlinedSubprogram]
                               , cuVariables   :: ![Variable]
                                 -- ^ Global variables in this unit
                               , cuRanges      :: ![Dwarf.Range]
                               , cuLNE         :: ![DW_LNE]
                               }

instance Show CompileUnit where
  show = show . pretty

instance Pretty CompileUnit where
  pretty cu =
    vcat [ text "producer:    " <+> text (cuProducer cu)
         , text "language:    " <+> text (show (cuLanguage cu))
         , text "name:        " <+> text (cuName cu)
         , text "comp_dir:    " <+> text (cuCompDir cu)
         , text "GNU_macros:  " <+> text (show (cuGNUMacros cu))
         , ppList "variables"           (pretty <$> cuVariables cu)
         , ppList "subprograms"         (pretty <$> cuSubprograms cu)
         , ppList "inlined subprograms" (pretty <$> cuInlinedSubprograms cu)
         , ppList "ranges"              (ppRange <$> cuRanges cu)
         ]

ppList :: String -> [Doc] -> Doc
ppList _ [] = text ""
ppList nm l = (text nm <> colon) <$$> indent 2 (vcat l)

data SectionContents = SecContents { debugLine :: !BS.ByteString
                                     -- ^ .debug_line section contents
                                   , debugRanges :: !BS.ByteString
                                     -- ^ .debug_ranges
                                   }

    -- Section 7.20 - Address Range Table
-- Returns the ranges that belong to a CU
getAddressRangeTable :: Endianess
                     -> Encoding
                     -> BS.ByteString
                     -> Parser [Dwarf.Range]
getAddressRangeTable end enc bs = parseGet bs (go [])
  where readAddress = desrGetOffset end enc
        go prev = do
          r <- Range <$> readAddress <*> readAddress
          if r /= Range 0 0 then
            go (r:prev)
           else
            pure $! reverse prev

parseCompileUnit :: Word64 -- ^ Expected number of bytes in a pointer.
                 -> SectionContents
                 -> (CUContext, DIE)
                 -> (Either String CompileUnit, [String])
parseCompileUnit w contents (ctx,d) =
 runParser w (cuReader ctx) $ runDIEParser "parseCompileUnit" d $ do
  checkTag DW_TAG_compile_unit
  let dr = cuReader ctx
  let end = drEndianess dr
  let tgt = drTarget64 dr
  prod      <- getSingleAttribute DW_AT_producer   attributeAsString
  lang      <- getMaybeAttribute  DW_AT_language   attributeAsLang
  name      <- getSingleAttribute DW_AT_name       attributeAsString
  compDir   <- getSingleAttribute DW_AT_comp_dir   attributeAsString
  -- Get offset into .debug_line for this compile units line number information
  (file_vec, lne) <- fmap (fromMaybe (V.empty, [])) $
    getMaybeAttribute DW_AT_stmt_list $ \v -> do
      offset <- attributeAsUInt v
      let lines_bs = debugLine contents
      when (fromIntegral offset > BS.length lines_bs) $ do
        fail "Illegal compile unit debug_line offset"
      let bs = BS.drop (fromIntegral offset) lines_bs
      (file_list, lne) <- parseGet bs (getLNE end tgt)
      pure (V.fromList file_list, lne)

  ranges <-
    if hasAttribute DW_AT_low_pc d then do
     lowPC    <- getSingleAttribute DW_AT_low_pc     attributeAsUInt
     if hasAttribute DW_AT_high_pc d then do
       highPC   <- getSingleAttribute DW_AT_high_pc    attributeAsUInt
       when (hasAttribute DW_AT_ranges d) $ do
         fail $ "Unexpected ranges"
       pure $! [Range lowPC (lowPC + highPC)]
      else do
        range_offset   <- getSingleAttribute DW_AT_ranges     attributeAsUInt
        lift $ getAddressRangeTable end (drEncoding dr) $
           BS.drop (fromIntegral range_offset) $ debugRanges contents
   else do
     when (hasAttribute DW_AT_high_pc d) $ do
       fail $ "Unexpected high_pc\n" ++ show d
     when (hasAttribute DW_AT_ranges d) $ do
       fail $ "Unexpected ranges\n" ++ show d
     pure []

  gnuMacros <- getMaybeAttribute DW_AT_GNU_macros attributeAsUInt
  -- Type map for children
  typeMap <- parseTypeMap file_vec


  (inlinedDies, subprogramDies) <-
    partition (hasAttribute DW_AT_abstract_origin) <$>
      parseChildrenList DW_TAG_subprogram pure

  subprograms <- lift $ traverse (parseSubprogram file_vec typeMap) subprogramDies
  let subMap = Map.fromList $ zipWith (\d' s -> (dieId d', s)) subprogramDies subprograms
  inlinedSubs <- lift $ traverse (parseInlinedSubprogram file_vec typeMap subMap) inlinedDies

  variables <- parseChildrenList DW_TAG_variable (parseVariable file_vec typeMap)

  pure $! CompileUnit { cuProducer           = prod
                      , cuLanguage           = lang
                      , cuName               = name
                      , cuCompDir            = compDir
                      , cuGNUMacros          = gnuMacros
                      , cuSubprograms        = subprograms
                      , cuInlinedSubprograms = inlinedSubs
                      , cuVariables   = variables
                      , cuRanges      = ranges
                      , cuLNE         = lne
                      }

------------------------------------------------------------------------
-- loadDwarf

tryGetElfSection :: BS.ByteString -> Elf.Elf v -> State [String] BS.ByteString
tryGetElfSection nm e =
  case Elf.findSectionByName nm e of
    [] -> do
      let msg = "Could not find " ++ show nm ++ " section."
      modify $ (:) msg
      pure $ BS.empty
    s:r  -> do
      when (not (null r)) $ do
        let msg = "Found multiple " ++ show nm ++ " sections."
        modify $ (:) msg
      pure $ Elf.elfSectionData s

-- | Return dwarf information out of an Elf file.
dwarfInfoFromElf :: Elf.Elf v -> ([String], [CompileUnit])
dwarfInfoFromElf e = do
  case Elf.findSectionByName ".debug_info" e of
    [] -> ([], [])
    _ -> flip evalState [] $ do
      debug_info   <- tryGetElfSection ".debug_info"   e
      debug_abbrev <- tryGetElfSection ".debug_abbrev" e
      debug_lines  <- tryGetElfSection ".debug_line"   e
      debug_ranges <- tryGetElfSection ".debug_ranges" e
      debug_str    <- tryGetElfSection ".debug_str"    e
      let sections = Sections { dsInfoSection   = debug_info
                              , dsAbbrevSection = debug_abbrev
                              , dsStrSection    = debug_str
                              }
      let w = fromIntegral $ Elf.elfClassByteWidth (Elf.elfClass e)
      let end =
            case Elf.elfData e of
              Elf.ELFDATA2LSB -> LittleEndian
              Elf.ELFDATA2MSB -> BigEndian
      let (cuDies, _m) = parseInfo end sections
      let contents = SecContents { debugLine   = debug_lines
                                 , debugRanges = debug_ranges
                                 }
      mdies <- forM cuDies $ \cuPair -> do
        let (mr, warnings) = parseCompileUnit w contents cuPair
        case mr of
          Left msg -> do
            modify $ ((msg:warnings) ++)
            pure Nothing
          Right cu -> do
            modify $ (warnings ++)
            pure $ Just cu
      warnings <- get
      pure (reverse warnings, catMaybes mdies)

-- | This returns all the variables in the given compile units.
dwarfGlobals :: [CompileUnit] -> [Variable]
dwarfGlobals units = fmap snd (sortOn fst l)
  where l = [ (w,var)
            | cu <- units
            , var <- cuVariables cu
            , w <- maybeToList (varLocation var)
            ]
