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
    Data.Macaw.Memory.Endianness(..)
  , Dwarf.Sections
  , Dwarf.mkSections
  , Dwarf.CUContext
  , Dwarf.cuOffset
  , Dwarf.CUOffset(..)
  , firstCUContext
  , Dwarf.nextCUContext
  , getCompileUnit
  , dwarfCompileUnits
  , CompileUnit(..)
  , dwarfGlobals
    -- ** Utility function
  , dwarfInfoFromElf
    -- * Variables
  , Variable(..)
    -- * Sub programs
  , Subprogram(..)
  , SubprogramDef(..)
    -- * Inlineing
  , SubprogramRef
  , VariableRef
    -- * Locations
  , Location(..)
  , DeclLoc(..)
    -- * Type information
  , TypeRef
  , typeRefFileOffset
  , AbsType
  , TypeApp(..)
  , StructDecl(..)
  , UnionDecl(..)
  , Member(..)
  , EnumDecl(..)
  , Enumerator(..)
  , SubroutineTypeDecl(..)
  , Subrange(..)
  , Typedef(..)
  , TypeQual(..)
  , TypeQualAnn(..)
    -- * Name and Description
  , Name(..)
  , Description(..)
    -- * Low-level access
  , DwarfExpr(..)
    -- * Exports of "Data.Dwarf"
  , Dwarf.DieID
  , Dwarf.DW_OP(..)
  , Dwarf.Range(..)
  ) where

import           Control.Lens
import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State
import           Data.Binary.Get
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Dwarf as Dwarf
import           Data.Dwarf as Dwarf hiding (Endianess(..), firstCUContext)
import qualified Data.ElfEdit as Elf
import           Data.Foldable
import           Data.Int
import           Data.List (sortOn)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.String
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Prettyprinter
import           Text.Printf

import           Data.Macaw.Memory (Endianness(..))

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

-- | A monad transformer that adds the ability to collect a list of messages
-- (called "warnings") and throw a exception.
newtype WarnT e m r = WarnT { unWarnT :: ExceptT e (StateT [e] m) r }
  deriving (Functor, Applicative, Monad, MonadError e)

runWarnT :: WarnT e m r -> m (Either e r, [e])
runWarnT m = runStateT (runExceptT (unWarnT m)) []

instance Monad m => WarnMonad e (WarnT e m) where
  warn msg = WarnT $ ExceptT $ StateT $ \s -> pure (Right (), msg : s)

  runInContext f m = WarnT $ ExceptT $ StateT $ \s -> do
    let g (mr, warnings) = (either (Left . f) Right mr, fmap f warnings ++ s)
     in g <$> runWarnT m

------------------------------------------------------------------------
-- Parser

-- | The context needed to read dwarf entries.
newtype ParserState = ParserState { readerInfo :: Dwarf.Reader
                                  }

newtype Parser r = Parser { unParser :: ReaderT ParserState (WarnT String Identity) r }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError String
           , WarnMonad String
           )


runParser :: Dwarf.Reader -> Parser r -> (Either String r, [String])
runParser dr p = runIdentity (runWarnT (runReaderT (unParser p) s))
  where s = ParserState { readerInfo = dr
                        }

------------------------------------------------------------------------
-- Parser functions

-- | Error from parsing an attribute.
data AttrError
   = IncorrectTypeFor !BSC.ByteString
   | InvalidFileIndex !Word64

ppAttrError :: AttrError -> String
ppAttrError e =
  case e of
    IncorrectTypeFor tp -> "Incorrect type for " <> BSC.unpack tp
    InvalidFileIndex idx -> "Invalid file index " ++ show idx

-- | A parser for attribute values.
type AttrParser r = Dwarf.Reader -> DW_ATVAL -> Except AttrError r

convertAttribute :: DW_AT
                 -> AttrParser r
                 -> DW_ATVAL
                 -> Parser r
convertAttribute dat f v = do
  dr <- Parser $ asks readerInfo
  case runExcept (f dr v) of
    Left e ->
      throwError $ "Could not interpret attribute "
        ++ show dat ++ " value " ++ show v ++ ": " ++ ppAttrError e
    Right r -> pure r

attributeValue :: AttrParser DW_ATVAL
attributeValue = \_ -> pure

attributeAsBlob :: AttrParser BS.ByteString
attributeAsBlob _ (DW_ATVAL_BLOB b) = pure b
attributeAsBlob _ _ = throwError $ IncorrectTypeFor "BLOB"

attributeAsBool :: AttrParser Bool
attributeAsBool _ (DW_ATVAL_BOOL b) = pure b
attributeAsBool _ _ = throwError $ IncorrectTypeFor "Bool"

attributeAsUInt :: AttrParser Word64
attributeAsUInt _ (DW_ATVAL_UINT u) = pure u
attributeAsUInt _ _ = throwError $ IncorrectTypeFor "UInt"

-- | Parse an attribute as a DIE identifier.
attributeAsDieID :: AttrParser DieID
attributeAsDieID _ (DW_ATVAL_REF r) = pure r
attributeAsDieID _ _ = throwError $ IncorrectTypeFor "DieID"

-- | Parse an attribute intended to be interpreted as a displayable
-- string.
--
-- The character set is not defined, but typically 7-bit ASCII.
attributeAsString :: AttrParser BS.ByteString
attributeAsString _ (DW_ATVAL_STRING s) = pure s
attributeAsString _ _ = throwError $ IncorrectTypeFor "String"

attributeAsBaseTypeEncoding :: AttrParser DW_ATE
attributeAsBaseTypeEncoding _ (DW_ATVAL_UINT u) = pure (DW_ATE u)
attributeAsBaseTypeEncoding _ _ = throwError $ IncorrectTypeFor "BaseTypeEncoding"

attributeAsLang :: AttrParser DW_LANG
attributeAsLang dr v = DW_LANG <$> attributeAsUInt dr v

mapAttr :: (a -> b) -> AttrParser a -> AttrParser b
mapAttr f p dr v = f <$> p dr v

parseGet :: BS.ByteString -> Get a -> Parser a
parseGet bs m =
  case pushEndOfInput (runGetIncremental m `pushChunk` bs) of
    Fail _ _ msg -> throwError msg
    Partial _ -> throwError "Unexpected partial"
    Done _ _ r -> pure r

------------------------------------------------------------------------
-- Range

ppRange :: Range -> Doc ann
ppRange (Range x y) =
    "low:" <+> pretty (showHex x "") <+> "high:" <+> pretty (showHex y "")

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

runDIEParser :: String
             -> DIE
             -> DIEParser r
             -> Parser r
runDIEParser ctx d act =
  runInContext (taggedError (ctx ++ " " ++ show (dieId d) ++ " " ++ show (dieTag d))) $ do
    let childMap :: Map DW_TAG [DIE]
        childMap = foldr' (\d' -> Map.insertWith (\_ o -> d' : o) (dieTag d') [d']) Map.empty (dieChildren d)
        attrMap  = foldr' (\(k,v) -> Map.insertWith (++) k [v])     Map.empty (dieAttributes d)
        s0 = DPS { dpsDIE = d
                 , dpsAttributeMap = attrMap
                 , _dpsSeenAttributes = Set.singleton DW_AT_sibling
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

getSingleAttribute :: DW_AT -> AttrParser v -> DIEParser v
getSingleAttribute dat p = do
  d <- gets dpsDIE
  m <- gets dpsAttributeMap
  case Map.findWithDefault [] dat m of
    [] -> throwError $ "Expected attribute " ++ show dat ++ " in " ++ show d ++ "."
    [v] -> do
      ignoreAttribute dat
      lift $ convertAttribute dat p v
    _ -> throwError $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

getAttributeWithDefault :: DW_AT -> v -> AttrParser v -> DIEParser v
getAttributeWithDefault dat def f = do
  d <- gets dpsDIE
  m <- gets dpsAttributeMap
  case Map.findWithDefault [] dat m of
    [] -> do
      ignoreAttribute dat
      pure def
    [v] -> do
      ignoreAttribute dat
      lift $ convertAttribute dat f v
    _ -> throwError $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

getMaybeAttribute :: DW_AT -> AttrParser v -> DIEParser (Maybe v)
getMaybeAttribute dat f = do
  d <- gets dpsDIE
  m <- gets dpsAttributeMap
  case Map.findWithDefault [] dat m of
    [] -> do
      ignoreAttribute dat
      pure Nothing
    [v] -> do
      ignoreAttribute dat
      lift $ Just <$> convertAttribute dat f v
    _ -> throwError $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

parseChildrenList :: DW_TAG -> (DIE -> Parser v) -> DIEParser [v]
parseChildrenList tag f = do
  ignoreChild tag
  m <- gets dpsChildrenMap
  lift $ traverse f $ Map.findWithDefault [] tag m

hasChildren :: DW_TAG -> DIEParser Bool
hasChildren tag = do
  ignoreChild tag
  gets $ Map.member tag . dpsChildrenMap


------------------------------------------------------------------------
-- DeclLoc

-- | Type synonym for file paths in Dwarf
--
-- The empty string denotes no file.
newtype DwarfFilePath = DwarfFilePath { filePathVal :: BS.ByteString }
  deriving (Eq, IsString)

instance Show DwarfFilePath where
  show = BSC.unpack . filePathVal

instance Pretty DwarfFilePath where
  pretty = pretty . BSC.unpack . filePathVal

-- | File vector read from line-number information.
type FileVec = V.Vector DwarfFilePath

-- | A file and line number for a declaration.
data DeclLoc = DeclLoc { locFile   :: !DwarfFilePath
                       , locLine   :: !Word64
                       , locColumn :: !Word64
                       }

instance Pretty DeclLoc where
  pretty loc =
    let file | locFile loc == "" = emptyDoc
             | otherwise = "decl_file:   " <+> pretty (locFile loc) <> line
        lne | locLine loc == 0 = emptyDoc
            | otherwise  = "decl_line:   " <+> pretty (locLine loc) <> line
        col | locColumn loc == 0 = emptyDoc
            | otherwise  = "decl_column: " <+> pretty (locColumn loc) <> line
     in file <> lne <> col

instance Show DeclLoc where
  show = show . pretty


attributeAsFile :: FileVec -> AttrParser DwarfFilePath
attributeAsFile fileVec _ (DW_ATVAL_UINT i) =
  if i == 0 then
    pure ""
   else if toInteger i <= toInteger (V.length fileVec) then
    pure $! fileVec V.! fromIntegral (i-1)
   else
    throwError $ InvalidFileIndex i
attributeAsFile _ _ _ = throwError $ IncorrectTypeFor "file path"


-- | Read the decl_file and decl_line attributes from the DIE
parseDeclLoc :: FileVec -> DIEParser DeclLoc
parseDeclLoc fileVec = do
  declFile   <- getAttributeWithDefault DW_AT_decl_file "" (attributeAsFile fileVec)
  declLine   <- getAttributeWithDefault DW_AT_decl_line   0 attributeAsUInt
  declCol    <- getAttributeWithDefault DW_AT_decl_column 0 attributeAsUInt
  pure $! DeclLoc { locFile = declFile
                  , locLine = declLine
                  , locColumn =declCol
                  }

------------------------------------------------------------------------
-- DW_OP operations

ppOp :: DW_OP -> Doc ann
ppOp (DW_OP_addr w) | w >= 0 = pretty (showHex w "")
ppOp o = viaShow o

ppOps :: [DW_OP] -> Doc ann
ppOps l = hsep (ppOp <$> l)

------------------------------------------------------------------------
-- Name and Descripion

newtype Name = Name { nameVal :: BS.ByteString }
  deriving (Eq, Ord)

instance IsString Name where
  fromString = Name . BSC.pack

instance Pretty Name where
  pretty = pretty . BSC.unpack . nameVal

instance Show Name where
  show = BSC.unpack . nameVal

-- | The value of a `DW_AT_description` field.
--
-- Note. This is the empty string if th
newtype Description = Description { descriptionVal :: BS.ByteString }

instance Show Description where
  show = BSC.unpack . descriptionVal


-- | Get name and description.
--
-- If name of description is missing, the empty string is returned.
getNameAndDescription :: DIEParser (Name, Description)
getNameAndDescription = do
  (,) <$> (Name        <$> getAttributeWithDefault DW_AT_name BS.empty attributeAsString)
      <*> (Description <$> getAttributeWithDefault DW_AT_description BS.empty attributeAsString)

------------------------------------------------------------------------
-- ConstValue

data ConstValue
  = ConstBlob BS.ByteString
  | ConstInt  Int64
  | ConstUInt Word64
  | ConstString BS.ByteString
    -- ^ A string of bytes that was originally null-terminated.
    --
    -- Note. The null terminator was removed and does not appear
    -- in the Haskell `ByteString`.
  deriving (Show)

attributeConstValue :: AttrParser ConstValue
attributeConstValue _ v =
  case v of
    DW_ATVAL_BLOB x   -> pure $! ConstBlob x
    DW_ATVAL_INT x    -> pure $! ConstInt  x
    DW_ATVAL_UINT x   -> pure $! ConstUInt x
    DW_ATVAL_STRING x -> pure $! ConstString x
    _ -> throwError $ IncorrectTypeFor "const value"

getConstValue :: DIEParser (Maybe ConstValue)
getConstValue = getMaybeAttribute DW_AT_const_value attributeConstValue

------------------------------------------------------------------------
-- TypeRef

-- | A reference to a type DIE
newtype TypeRef = TypeRef DieID
  deriving (Eq, Ord, Show)

-- | Return the offset asssociated with the type.
typeRefFileOffset :: TypeRef -> Word64
typeRefFileOffset (TypeRef o) = dieID o

instance Pretty TypeRef where
  pretty r = pretty (showHex (typeRefFileOffset r) "")

------------------------------------------------------------------------
-- Enumerator

data Enumerator = Enumerator { enumName :: !Name
                             , enumDescription :: !Description
                             , enumValue :: !ConstValue
                             }
  deriving (Show)

parseEnumerator :: DIE -> Parser Enumerator
parseEnumerator d = runDIEParser "parseEnumerator" d $ do
  checkTag DW_TAG_enumerator
  (name, desc) <- getNameAndDescription
  val <- getSingleAttribute DW_AT_const_value attributeConstValue
  pure Enumerator { enumName        = name
                  , enumDescription = desc
                  , enumValue       = val
                  }

------------------------------------------------------------------------
-- Subrange

data Subrange tp = Subrange { subrangeType :: tp
                            , subrangeUpperBound :: [DW_OP]
                            }
  deriving (Show)


--subrangeTypeLens :: Lens (Subrange a) (Subrange b) a b
--subrangeTypeLens = lens subrangeType (\s v -> s { subrangeType = v })

parseSubrange :: DIE -> Parser (Subrange TypeRef)
parseSubrange d = runDIEParser "parseSubrange" d $ do
  dr <- lift $ Parser $ asks readerInfo
  tp       <- getSingleAttribute DW_AT_type attributeAsTypeRef
  upperVal <- getSingleAttribute DW_AT_upper_bound attributeValue

  upper <-
    case upperVal of
      DW_ATVAL_UINT w -> pure [DW_OP_const8u w]
      DW_ATVAL_BLOB bs ->
        case parseDW_OPs dr bs of
          Left (_, _, msg) -> throwError msg
          Right ops -> pure ops
      _ -> throwError "Invalid upper bound"

  pure $! Subrange { subrangeType = tp
                   , subrangeUpperBound = upper
                   }

------------------------------------------------------------------------
-- Type

{-
data BaseType = BaseTypeDef { baseSize     :: !Word64
                            , baseEncoding :: !DW_ATE
                            , baseName     :: !String
                            }
  deriving (Show)
-}

data Member = Member { memberName     :: !Name
                     , memberDescription :: !Description
                     , memberDeclLoc  :: !DeclLoc
                     , memberLoc      :: !(Maybe Word64)
                     , memberType     :: !TypeRef
                     , memberArtificial :: !Bool
                     , memberByteSize   :: !(Maybe Word64)
                     , memberBitOffset  :: !(Maybe Word64)
                     , memberBitSize    :: !(Maybe Word64)
                     }
  deriving (Show)

data StructDecl = StructDecl { structName     :: !Name
                             , structDescription :: !Description
                             , structByteSize :: !Word64
                             , structLoc      :: !DeclLoc
                             , structMembers  :: ![Member]
                             }
  deriving (Show)

data UnionDecl = UnionDecl { unionName     :: !Name
                           , unionDescription :: !Description
                           , unionByteSize :: !Word64
                           , unionLoc      :: !DeclLoc
                           , unionMembers  :: ![Member]
                           }
  deriving (Show)

data EnumDecl = EnumDecl { enumDeclName     :: !Name
                         , enumDeclDescription :: !Description
                         , enumDeclByteSize :: !Word64
                         , enumDeclLoc      :: !DeclLoc
                           -- | The underlying type of an enum.
                         , enumDeclType     :: !(Maybe TypeRef)
                         , enumDeclCases    :: ![Enumerator]
                         }
  deriving (Show)

data SubroutineTypeDecl
   = SubroutineTypeDecl { fntypePrototyped :: !(Maybe Bool)
                        , fntypeFormals    :: ![DIE]
                        , fntypeType       :: !(Maybe TypeRef)
                        }
  deriving (Show)

data Typedef = Typedef { typedefName :: !Name
                       , typedefDescription :: !Description
                       , typedefLoc  :: !DeclLoc
                       , typedefType :: !TypeRef
                       }
  deriving (Show)

parseMember :: FileVec -> DIE -> Parser Member
parseMember fileVec d = runDIEParser "parseMember" d $ do
  checkTag DW_TAG_member
  (name, desc) <- getNameAndDescription
  tp         <- getSingleAttribute DW_AT_type attributeAsTypeRef
  memLoc     <- getMaybeAttribute  DW_AT_data_member_location  attributeAsUInt
  artificial <- getAttributeWithDefault DW_AT_artificial False attributeAsBool
  dloc <- parseDeclLoc fileVec

  byteSize <- getMaybeAttribute DW_AT_byte_size  attributeAsUInt
  bitOff   <- getMaybeAttribute DW_AT_bit_offset attributeAsUInt
  bitSize  <- getMaybeAttribute DW_AT_bit_size   attributeAsUInt

  pure $! Member { memberName = name
                 , memberDescription = desc
                 , memberDeclLoc  = dloc
                 , memberLoc = memLoc
                 , memberType = tp
                 , memberArtificial = artificial
                 , memberByteSize  = byteSize
                 , memberBitOffset = bitOff
                 , memberBitSize   = bitSize
                 }

attributeAsTypeRef :: AttrParser TypeRef
attributeAsTypeRef _ (DW_ATVAL_REF r) = pure (TypeRef r)
attributeAsTypeRef _ _ = throwError $ IncorrectTypeFor "type reference"

-- | A qualifier on a type.
data TypeQual
   = ConstQual
   | VolatileQual
   | RestrictQual
  deriving (Show)

-- | A type qualifier annotation.
data TypeQualAnn = TypeQualAnn { tqaTypeQual :: !TypeQual
                               , tqaName     :: !Name
                               , tqaDescription :: !Description
                               , tqaDeclLoc     :: !DeclLoc
                               , tqaAlign       :: !Word64
                               , tqaType        :: !(Maybe TypeRef)
                               }
  deriving (Show)

-- | A type form
data TypeApp
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
   | LongDoubleType
     -- ^ A long double type.
   | UnsignedCharType
     -- ^ A 1-byte unsigned character.
   | SignedCharType
     -- ^ A 1-byte signed character.

   | ArrayType !TypeRef ![Subrange TypeRef]
   | PointerType !(Maybe Word64) !(Maybe TypeRef)
     -- ^ @PointerType mw mtp@ describes a pointer where @mtp@ is
     -- the type that the pointer points to (or 'Nothing') to indicate
     -- this is a void pointer.  @mw@ is the number of bytes the pointer
     -- occupies or @Nothing@ to indicate that is omitted.
   | StructType !StructDecl
     -- ^ Denotes a C struct
   | UnionType !UnionDecl
     -- ^ Denotes a C union
   | EnumType !EnumDecl
   | SubroutinePtrType !SubroutineTypeDecl
   | TypedefType !Typedef
   | TypeQualType !TypeQualAnn
     -- ^ Restrict modifier on type.
   | SubroutineTypeF !SubroutineTypeDecl
     -- ^ Subroutine type
  deriving (Show)

-- | A type parser takes the file vector and returns either a `TypeF` or `Nothing`.
--
-- The nothing value is returned, because `DW_TAG_const_type` with no `DW_AT_type`
-- attribute.
type TypeParser = FileVec -> DIEParser TypeApp

parseBaseType :: TypeParser
parseBaseType _ = do
  (name, _) <- getNameAndDescription
  enc  <- getSingleAttribute DW_AT_encoding  attributeAsBaseTypeEncoding
  size <- getSingleAttribute DW_AT_byte_size attributeAsUInt
  case (name, enc,size) of
    (_, DW_ATE_boolean, 1) -> pure $ BoolType
    (_, DW_ATE_signed,   _) | size >= 1 -> pure $ SignedIntType (fromIntegral size)
    (_, DW_ATE_unsigned, _) | size >= 1 -> pure $ UnsignedIntType (fromIntegral size)

    (_, DW_ATE_float,    4) -> pure $! FloatType
    (_, DW_ATE_float,    8) -> pure $! DoubleType
    ("long double", DW_ATE_float, 16) -> pure $! LongDoubleType

    (_, DW_ATE_signed_char, 1)   -> pure $! SignedCharType
    (_, DW_ATE_unsigned_char, 1) -> pure $! UnsignedCharType
    _ -> throwError $ "Unsupported base type " ++ show name ++ " " ++ show enc ++ " " ++ show size

parsePointerType :: TypeParser
parsePointerType _ = do
  mtp <- getMaybeAttribute DW_AT_type attributeAsTypeRef
  w   <- getMaybeAttribute DW_AT_byte_size attributeAsUInt
  pure $! PointerType w mtp

parseStructureType :: TypeParser
parseStructureType fileVec = do
  (name, desc) <- getNameAndDescription
  byteSize  <- getSingleAttribute DW_AT_byte_size  attributeAsUInt
  dloc    <- parseDeclLoc fileVec

  members <- parseChildrenList DW_TAG_member $ parseMember fileVec

  let struct = StructDecl { structName     = name
                          , structDescription = desc
                          , structByteSize = byteSize
                          , structLoc      = dloc
                          , structMembers  = members
                          }
  pure $! StructType struct

parseUnionType :: TypeParser
parseUnionType fileVec = do
  (name, desc) <- getNameAndDescription
  byteSize  <- getSingleAttribute DW_AT_byte_size  attributeAsUInt
  dloc    <- parseDeclLoc fileVec

  members <- parseChildrenList DW_TAG_member $ parseMember fileVec

  let u = UnionDecl { unionName     = name
                    , unionDescription = desc
                    , unionByteSize = byteSize
                    , unionLoc      = dloc
                    , unionMembers  = members
                    }
  pure $! UnionType u

parseTypedefType :: TypeParser
parseTypedefType fileVec = do
  (name, desc) <- getNameAndDescription
  dloc    <- parseDeclLoc fileVec
  tp <- getSingleAttribute DW_AT_type attributeAsTypeRef

  let td = Typedef { typedefName = name
                   , typedefDescription = desc
                   , typedefLoc  = dloc
                   , typedefType = tp
                   }
  pure $! TypedefType td

parseArrayType :: TypeParser
parseArrayType _ = do
  eltType <- getSingleAttribute DW_AT_type attributeAsTypeRef

  sr <- parseChildrenList DW_TAG_subrange_type parseSubrange
  pure $! ArrayType eltType sr

parseEnumerationType :: TypeParser
parseEnumerationType fileVec = do
  (name, desc) <- getNameAndDescription
  byteSize     <- getSingleAttribute DW_AT_byte_size  attributeAsUInt
  dloc           <- parseDeclLoc fileVec
  _enc           <- getMaybeAttribute DW_AT_encoding attributeAsBaseTypeEncoding
  underlyingType <- getMaybeAttribute DW_AT_type attributeAsTypeRef
  cases <- parseChildrenList DW_TAG_enumerator parseEnumerator
  let e = EnumDecl { enumDeclName     = name
                   , enumDeclDescription = desc
                   , enumDeclByteSize = byteSize
                   , enumDeclType     = underlyingType
                   , enumDeclLoc      = dloc
                   , enumDeclCases    = cases
                   }
  pure $! EnumType e

-- | Parse a subroutine type.
parseSubroutineType :: TypeParser
parseSubroutineType _ = do
  proto <- getMaybeAttribute DW_AT_prototyped attributeAsBool
  formals <- parseChildrenList DW_TAG_formal_parameter pure

  tp <- getMaybeAttribute DW_AT_type attributeAsTypeRef

  let sub = SubroutineTypeDecl { fntypePrototyped = proto
                               , fntypeFormals    = formals
                               , fntypeType       = tp
                               }
  pure $! SubroutineTypeF sub

parseTypeQualifier :: TypeQual -> TypeParser
parseTypeQualifier tq fileVec = do
  (name, desc) <- getNameAndDescription
  loc   <- parseDeclLoc fileVec
  alignment <- getAttributeWithDefault DW_AT_alignment 0 attributeAsUInt
  mtp   <- getMaybeAttribute DW_AT_type attributeAsTypeRef
  let ann = TypeQualAnn { tqaTypeQual = tq
                        , tqaName = name
                        , tqaDescription = desc
                        , tqaDeclLoc = loc
                        , tqaAlign = alignment
                        , tqaType = mtp
                        }
  pure $! TypeQualType ann

typeParsers :: Map DW_TAG TypeParser
typeParsers = Map.fromList
  [ (,) DW_TAG_base_type        parseBaseType
  , (,) DW_TAG_const_type       (parseTypeQualifier ConstQual)
  , (,) DW_TAG_volatile_type    (parseTypeQualifier VolatileQual)
  , (,) DW_TAG_restrict_type    (parseTypeQualifier RestrictQual)
  , (,) DW_TAG_pointer_type     parsePointerType
  , (,) DW_TAG_structure_type   parseStructureType
  , (,) DW_TAG_union_type       parseUnionType
  , (,) DW_TAG_typedef          parseTypedefType
  , (,) DW_TAG_array_type       parseArrayType
  , (,) DW_TAG_enumeration_type parseEnumerationType
  , (,) DW_TAG_subroutine_type  parseSubroutineType
  ]

type AbsType = (Either String TypeApp, [String])

-- | Parse a type given a vector identifying file vectors.
parseTypeMap :: Map TypeRef AbsType
             -> FileVec
             -> DIEParser (Map TypeRef AbsType)
parseTypeMap preMap fileVec = do
  mapM_ ignoreChild  (Map.keys typeParsers)
  dr <- lift $ Parser $ asks readerInfo
  childMap <- gets dpsChildrenMap
  let insDIE :: TypeParser
             -> Map TypeRef AbsType
             -> DIE
             -> Map TypeRef AbsType
      insDIE act m d =
        Map.insert (TypeRef (dieId d))
                   (runParser dr (runDIEParser "parseTypeF" d (act fileVec)))
                   m

  let insTagChildren :: Map TypeRef AbsType
                     -> DW_TAG
                     -> TypeParser
                     -> Map TypeRef AbsType
      insTagChildren m tag act =
        foldl' (insDIE act) m (Map.findWithDefault [] tag childMap)

  pure $! Map.foldlWithKey' insTagChildren preMap typeParsers

------------------------------------------------------------------------
-- Location

data DwarfExpr = DwarfExpr !Dwarf.Reader !BS.ByteString

instance Eq DwarfExpr where
  DwarfExpr _ x == DwarfExpr _ y = x == y

instance Ord DwarfExpr where
  compare (DwarfExpr _ x) (DwarfExpr _ y) = compare x y

instance Show DwarfExpr where
  show (DwarfExpr dr bs) =
    case Dwarf.parseDW_OPs dr bs of
      Left (_, _, msg) -> msg
      Right r -> show r

-- | Provides a way of computing the location of a variable.
data Location
   = ComputedLoc !DwarfExpr
   | OffsetLoc !Word64
  deriving (Eq,Ord)

attributeAsLocation :: AttrParser Location
attributeAsLocation dr = \case
  DW_ATVAL_BLOB b -> pure (ComputedLoc (DwarfExpr dr b))
  DW_ATVAL_UINT w -> pure (OffsetLoc w)
  _ -> throwError $ IncorrectTypeFor "Location"

instance Pretty Location where
  pretty (ComputedLoc (DwarfExpr dr bs)) =
    case Dwarf.parseDW_OPs dr bs of
      Left (_, _, msg) -> pretty msg
      Right ops -> ppOps ops
  pretty (OffsetLoc w) = pretty ("offset 0x" ++ showHex w "")

------------------------------------------------------------------------
-- Variable

-- | A reference to a variable
newtype VariableRef = VariableRef DieID
  deriving (Eq,Ord)

instance Pretty VariableRef where
  pretty (VariableRef (DieID w)) = pretty ("0x" ++ showHex w "")

data Variable = Variable { varDieID    :: !DieID
                         , varName     :: !Name
                         , varDescription :: !Description
                         , varDecl     :: !Bool
                           -- ^ Indicates if this variable is just a declaration
                         , varDeclLoc  :: !DeclLoc
                         , varType     :: !(Maybe TypeRef)
                         , varLocation :: !(Maybe Location)
                         , varConstValue :: !(Maybe ConstValue)
                         , varOrigin :: !(Maybe VariableRef)
                           -- ^ A variable reference if this variable comes from an inlined function.
                         }

instance Pretty Variable where
  pretty v =
    vcat
    [ "name:    " <+> pretty (varName v)
    , pretty (varDeclLoc v)
    , "type:    " <+> pretty (varType v)
    , maybe ("") (\l -> "location:" <+> pretty l) (varLocation v)
    ]

instance Show Variable where
   show = show . pretty

------------------------------------------------------------------------
-- Variable

parseVariableOrParameter :: String -> FileVec -> DIE -> Parser Variable
parseVariableOrParameter nm fileVec d =
  runDIEParser nm d $ do
    mloc       <- getMaybeAttribute DW_AT_location attributeAsLocation
    (name, desc) <- getNameAndDescription
    dloc    <- parseDeclLoc fileVec
    mvarType    <- getMaybeAttribute DW_AT_type attributeAsTypeRef

    constVal   <- getConstValue

    decl  <- getAttributeWithDefault DW_AT_declaration False attributeAsBool
    _exte <- getMaybeAttribute DW_AT_external attributeAsBool

    ignoreAttribute DW_AT_artificial
    ignoreAttribute DW_AT_specification
    originDieID <- getMaybeAttribute DW_AT_abstract_origin attributeAsDieID

    pure $! Variable { varDieID    = dieId d
                     , varName     = name
                     , varDescription = desc
                     , varDecl     = decl
                     , varDeclLoc  = dloc
                     , varType     = mvarType
                     , varLocation = mloc
                     , varConstValue = constVal
                     , varOrigin = VariableRef <$> originDieID
                     }

parseVariables :: FileVec -> DIEParser [Variable]
parseVariables fileVec = do
  parseChildrenList DW_TAG_variable $
    parseVariableOrParameter "parseVariable" fileVec

parseParameters :: FileVec -> DIEParser [Variable]
parseParameters fileVec = do
  parseChildrenList DW_TAG_formal_parameter  $
    parseVariableOrParameter "parseParameter" fileVec

------------------------------------------------------------------------
-- Subprogram

-- | A reference to a subprogram.
newtype SubprogramRef = SubprogramRef DieID
  deriving (Eq, Ord)

instance Pretty SubprogramRef where
  pretty (SubprogramRef (DieID d)) = pretty ("0x" ++ showHex d "")

data SubprogramDef = SubprogramDef { subLowPC :: !(Maybe Word64)
                                   , subHighPC :: !(Maybe Word64)
                                   , subFrameBase  :: !(Maybe DwarfExpr)
                                   , subGNUAllCallSites :: !(Maybe Bool)
                                   }

instance Pretty SubprogramDef where
  pretty d =
     vcat [ "low_pc:     " <+> pretty (maybe "UNDEF" (`showHex` "") (subLowPC  d))
          , "high_pc:    " <+> pretty (maybe "UNDEF" (`showHex` "") (subHighPC d))
          , "frame_base: " <+> viaShow (subFrameBase d)
          , "GNU_all_call_sites: " <+> viaShow (subGNUAllCallSites d)
          ]

-- | Get `DW_AT_GNU_all_tail_call_sites`
getAllTailCallSites :: DIEParser Bool
getAllTailCallSites = getAttributeWithDefault DW_AT_GNU_all_tail_call_sites False attributeAsBool

parseSubprogramDef :: DIEParser SubprogramDef
parseSubprogramDef = do
  dr <- lift $ Parser $ asks readerInfo
  lowPC      <- getMaybeAttribute DW_AT_low_pc     attributeAsUInt
  highPC     <- getMaybeAttribute DW_AT_high_pc    attributeAsUInt
  frameBase  <- getMaybeAttribute DW_AT_frame_base attributeAsBlob
  callSites  <- getMaybeAttribute  DW_AT_GNU_all_call_sites attributeAsBool
  ignoreChild DW_TAG_lexical_block
  ignoreChild DW_TAG_GNU_call_site
  ignoreChild DW_TAG_inlined_subroutine
  pure $ SubprogramDef { subLowPC     = lowPC
                       , subHighPC    = highPC
                       , subFrameBase = DwarfExpr dr <$> frameBase
                       , subGNUAllCallSites = callSites
                       }

data Subprogram = Subprogram { subName        :: !Name
                             , subDescription :: !Description
                             , subLinkageName :: !BS.ByteString
                             , subExternal    :: !Bool
                             , subOrigin      :: !(Maybe SubprogramRef)
                               -- ^ Origin for inlined functions.
                             , subIsDeclaration :: !Bool
                               -- ^ Indicates this is a declaration and not a defining declaration.
                             , subEntryPC     :: !(Maybe Word64)
                             , subArtificial  :: !Bool
                             , subGNUAllTailCallSites :: !Bool
                             , subDeclLoc     :: !DeclLoc
                             , subPrototyped  :: !Bool
                             , subDef         :: !(Maybe SubprogramDef)
                             , subVars        :: !(Map VariableRef Variable)
                               -- | Maps variable ref to subprogram variable.
                               --
                               -- Note. Parameters offsets are ordered so in-order
                               -- traversal of map is order of parameters.
                             , subParamMap    :: !(Map VariableRef Variable)
                             , subUnspecifiedParams :: !Bool
                             , subRetType     :: !(Maybe TypeRef)
                               -- | Flag indicating function declared with
                               -- "noreturn" attribute
                             , subNoreturn    :: !Bool
                               -- | Type map for resolving types in subprogram.
                             , subTypeMap     :: !(Map TypeRef AbsType)
                             }

instance Pretty Subprogram where
  pretty sub =
    vcat [ "name:       " <+> pretty (subName sub)
         , "external:   " <+> viaShow (subExternal sub)
         , pretty (subDeclLoc sub)
         , "prototyped: " <+> viaShow (subPrototyped sub)
         , maybe ("") pretty (subDef sub)
         , ppList "variables" (pretty <$> Map.elems (subVars sub))
         , ppList "parameters" (pretty <$> Map.elems (subParamMap sub))
         , "return type: " <+> pretty (subRetType sub)
         ]

instance Show Subprogram where
  show = show . pretty

isInlined :: DW_INL -> Parser Bool
isInlined inl =
  case inl of
    DW_INL_not_inlined          -> pure False
    DW_INL_inlined              -> pure True
    DW_INL_declared_not_inlined -> pure False
    DW_INL_declared_inlined     -> pure True
    _ -> do
      warn "Unexpected inline attribute."
      pure False

-- | For some reason, DW_AT_linkage_name is duplicated in some elf files,
-- so we handle this specially.
getLinkageName ::  DIEParser BS.ByteString
getLinkageName = do
  let attrName = DW_AT_linkage_name
  ignoreAttribute attrName
  m <- gets dpsAttributeMap
  case Map.findWithDefault [] attrName m of
    [] -> do
      pure BS.empty
    v:r -> do
      d <- gets dpsDIE
      linkageName <- lift $ convertAttribute attrName attributeAsString v
      forM_ r $ \rv -> do
        case rv of
          DW_ATVAL_STRING rvs | rvs == linkageName -> pure ()
          _ -> throwError $ printf "Found distinct attributes for %s in %d." (show attrName) (show d)
      pure linkageName

getInlineAttribute :: DIEParser DW_INL
getInlineAttribute =
  getAttributeWithDefault DW_AT_inline DW_INL_not_inlined (mapAttr DW_INL attributeAsUInt)

-- | Parse a subprogram
--
-- Tag has type `DW_TAG_subprogram`
parseSubprogram :: FileVec
                -> Map TypeRef AbsType
                -> DIE
                -> Parser Subprogram
parseSubprogram fileVec typeMap d = runDIEParser "parseSubprogram" d $ do
  checkTag DW_TAG_subprogram
  ext  <- getAttributeWithDefault DW_AT_external    False attributeAsBool
  decl <- getAttributeWithDefault DW_AT_declaration False attributeAsBool

  inl <-  getInlineAttribute
  inlined <- lift $ isInlined inl

  originDieID <- getMaybeAttribute DW_AT_abstract_origin attributeAsDieID

  def <-
    if decl || inlined then
      pure Nothing
     else do
      Just <$> parseSubprogramDef

  (name, desc) <- getNameAndDescription
  linkageName <- getLinkageName
  prototyped <- getAttributeWithDefault DW_AT_prototyped False attributeAsBool
  artificial <- getAttributeWithDefault DW_AT_artificial False attributeAsBool
  dloc <- parseDeclLoc fileVec

  typeMap' <- parseTypeMap typeMap fileVec
  vars <- parseVariables fileVec
  -- DW_TAG_formal_paramters children
  params <- parseParameters fileVec
  hasUnspecifiedParams <- hasChildren DW_TAG_unspecified_parameters

  entryPC <- getMaybeAttribute DW_AT_entry_pc     attributeAsUInt

  retType <- getMaybeAttribute DW_AT_type attributeAsTypeRef
  noreturn <- getAttributeWithDefault DW_AT_noreturn False attributeAsBool

  allTailCallSites <- getAllTailCallSites

  ignoreAttribute DW_AT_type
  ignoreChild DW_TAG_label
  ignoreChild DW_TAG_lexical_block
  pure $! Subprogram { subName       = name
                     , subDescription = desc
                     , subLinkageName = linkageName
                     , subExternal   = ext
                     , subOrigin     = SubprogramRef <$> originDieID
                     , subIsDeclaration = decl
                     , subEntryPC    = entryPC
                     , subArtificial = artificial
                     , subGNUAllTailCallSites = allTailCallSites
                     , subDeclLoc    = dloc
                     , subPrototyped = prototyped
                     , subDef        = def
                     , subVars       = Map.fromList [ (VariableRef (varDieID v), v) | v <- vars ]
                     , subParamMap   = Map.fromList [ (VariableRef (varDieID v), v) | v <- params ]
                     , subUnspecifiedParams = hasUnspecifiedParams
                     , subRetType    = retType
                     , subNoreturn   = noreturn
                     , subTypeMap    = typeMap'
                     }

-- CompileUnit

-- | The output of one compilation.
data CompileUnit = CompileUnit { cuCtx :: !CUContext
                               , cuProducer    :: !BS.ByteString
                               , cuLanguage    :: Maybe DW_LANG
                               , cuName        :: !Name
                               , cuDescription :: !Description
                               , cuCompDir     :: !BS.ByteString
                               , cuGNUMacros   :: !(Maybe Word64)
                               , cuSubprogramMap :: !(Map SubprogramRef Subprogram)
                                 -- ^ Map from subprogram reference to a subprogram.
                               , cuSubprograms :: ![Subprogram]
                               , cuVariables   :: ![Variable]
                                 -- ^ Global variables in this unit
                               , cuTypeMap     :: !(Map TypeRef AbsType)
                               , cuRanges      :: ![Dwarf.Range]
                               , cuLNE         :: ![DW_LNE]
                               , cuFileVec     :: !FileVec
                                 -- ^ File vector for file references.
                               }

instance Show CompileUnit where
  show = show . pretty

instance Pretty CompileUnit where
  pretty cu =
    vcat [ "producer:    " <+> pretty (BSC.unpack (cuProducer cu))
         , "language:    " <+> viaShow (cuLanguage cu)
         , "name:        " <+> pretty (cuName cu)
         , "comp_dir:    " <+> pretty (BSC.unpack (cuCompDir cu))
         , "GNU_macros:  " <+> viaShow (cuGNUMacros cu)
         , ppList "variables"           (pretty <$> cuVariables cu)
         , ppList "subprograms"         (pretty <$> cuSubprograms cu)
         , ppList "ranges"              (ppRange <$> cuRanges cu)
         ]

ppList :: String -> [Doc ann] -> Doc ann
ppList nm [] = pretty nm <> ": []"
ppList nm l = vcat [pretty nm <> colon, indent 2 (vcat l)]

-- Section 7.20 - Address Range Table
-- Returns the ranges that belong to a CU
getAddressRangeTable :: Dwarf.Endianess
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

parseCompileUnit :: (CUContext, DIE)
                 -> (Either String CompileUnit, [String])
parseCompileUnit (ctx, d) =
 runParser (cuReader ctx) $ runDIEParser "parseCompileUnit" d $ do
  let contents = cuSections ctx
  checkTag DW_TAG_compile_unit
  let dr = cuReader ctx
  let end = drEndianess dr
  let tgt = drTarget64 dr
  prod      <- getSingleAttribute DW_AT_producer   attributeAsString
  lang      <- getMaybeAttribute  DW_AT_language   attributeAsLang
  (name, desc) <- getNameAndDescription
  compDir   <- getSingleAttribute DW_AT_comp_dir   attributeAsString
  -- Get offset into .debug_line for this compile units line number information
  mStmtOffset <- getMaybeAttribute DW_AT_stmt_list attributeAsUInt
  (fileVec, lne) <-
    case mStmtOffset of
      Nothing -> pure (V.empty, [])
      Just offset -> do
        let lines_bs = dsLineSection contents
        when (fromIntegral offset > BS.length lines_bs) $ do
          throwError "Illegal compile unit debug_line offset"
        let bs = BS.drop (fromIntegral offset) lines_bs
        (fileList, lne) <- lift $ parseGet bs (getLNE end tgt)
        pure (fmap DwarfFilePath (V.fromList fileList), lne)

  ranges <-
    if hasAttribute DW_AT_low_pc d then do
     lowPC    <- getSingleAttribute DW_AT_low_pc     attributeAsUInt
     if hasAttribute DW_AT_high_pc d then do
       highPC   <- getSingleAttribute DW_AT_high_pc    attributeAsUInt
       when (hasAttribute DW_AT_ranges d) $ do
         throwError $ "Unexpected ranges"
       pure $! [Range lowPC (lowPC + highPC)]
      else do
        range_offset   <- getSingleAttribute DW_AT_ranges     attributeAsUInt
        lift $ getAddressRangeTable end (drEncoding dr) $
           BS.drop (fromIntegral range_offset) $ dsRangesSection contents
   else do
     when (hasAttribute DW_AT_high_pc d) $ do
       throwError $ "Unexpected high_pc\n" ++ show d
     when (hasAttribute DW_AT_ranges d) $ do
       throwError $ "Unexpected ranges\n" ++ show d
     pure []

  gnuMacros <- getMaybeAttribute DW_AT_GNU_macros attributeAsUInt
  -- Type map for children
  typeMap <- parseTypeMap Map.empty fileVec


  subprogramDies <- parseChildrenList DW_TAG_subprogram pure

  subprograms <- lift $ traverse (parseSubprogram fileVec typeMap) subprogramDies
  let subMap = Map.fromList $ zipWith (\d' s -> (SubprogramRef (dieId d'), s)) subprogramDies subprograms
  variables <- parseVariables fileVec

  ignoreChild DW_TAG_dwarf_procedure

  pure $! CompileUnit { cuCtx                = ctx
                      , cuProducer           = prod
                      , cuLanguage           = lang
                      , cuName               = name
                      , cuDescription        = desc
                      , cuCompDir            = compDir
                      , cuGNUMacros          = gnuMacros
                      , cuSubprogramMap      = subMap
                      , cuSubprograms        = subprograms
                      , cuVariables   = variables
                      , cuTypeMap     = typeMap
                      , cuRanges      = ranges
                      , cuLNE         = lne
                      , cuFileVec     = fileVec
                      }

------------------------------------------------------------------------
-- dwarfCompileUnits

getCompileUnit :: CUContext -> (Either String CompileUnit, [String])
getCompileUnit ctx =
  case cuFirstDie ctx of
    Left e -> (Left e, [])
    Right d -> parseCompileUnit (ctx, d)

firstCUContext :: Endianness -> Dwarf.Sections -> Maybe (Either String CUContext)
firstCUContext end sections = do
  let dwEnd = case end of
                LittleEndian -> Dwarf.LittleEndian
                BigEndian    -> Dwarf.BigEndian
  Dwarf.firstCUContext dwEnd sections

{-# DEPRECATED dwarfCompileUnits "Use firstCUContext, nextCUContext and getCompileUnit" #-}

-- | Return dwarf information out of buffers.
dwarfCompileUnits:: Endianness
                 -> Dwarf.Sections
                 -> ([String], [CompileUnit])
dwarfCompileUnits end sections = do
  let go :: [String]
         -> [CompileUnit]
         -> Maybe (Either String CUContext)
         -> ([String], [CompileUnit])
      go prevWarn cus Nothing = (reverse prevWarn, reverse cus)
      go prevWarn cus (Just (Left e)) = (reverse (e:prevWarn), reverse cus)
      go prevWarn cus (Just (Right ctx)) =
        case getCompileUnit ctx of
          (Left msg, warnings) ->
            go (warnings ++ msg:prevWarn) cus (nextCUContext ctx)
          (Right cu, warnings) ->
            go (warnings ++ prevWarn) (cu:cus) (nextCUContext ctx)
   in go [] [] (firstCUContext end sections)

------------------------------------------------------------------------
-- dwarfInfoFromElf

-- | Elf informaton
tryGetElfSection :: Elf.Elf v -> BS.ByteString -> State [String] BS.ByteString
tryGetElfSection e nm =
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
    _ ->
      let end =
            case Elf.elfData e of
              Elf.ELFDATA2LSB -> LittleEndian
              Elf.ELFDATA2MSB -> BigEndian
          (sections, bufWarn) = runState (mkSections (tryGetElfSection e)) []
          (cuWarn, cu) = dwarfCompileUnits end sections
       in (reverse bufWarn ++ cuWarn, cu)

-- | This returns all the variables in the given compile units.
dwarfGlobals :: [CompileUnit] -> [Variable]
dwarfGlobals units = fmap snd (sortOn fst l)
  where l = [ (w,var)
            | cu <- units
            , var <- cuVariables cu
            , w <- maybeToList (varLocation var)
            ]
