{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Data.Macaw.Dwarf
  ( loadDwarf
  , dwarfGlobals
  ) where

import           Control.Lens
import           Control.Monad
import           Data.Binary.Get
import qualified Data.ByteString as BS
import           Data.Either
import           Data.ElfEdit
import           Data.List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import           Data.Word
import           Numeric (showHex)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Debug.Trace

import DWARF.Basics
import DWARF.DIE

--import           Data.Dwarf as Dwarf

-- pattern DW_TAG_XXXX              =  DW_TAG_user 137

pattern DW_AT_GNU_all_tail_call_sites = DW_AT_user 0x2116
pattern DW_AT_GNU_all_call_sites      = DW_AT_user 0x2117
pattern DW_AT_GNU_macros              = DW_AT_user 0x2119

getAttribute :: DIE -> DW_AT -> [DW_ATVAL]
getAttribute d dat = snd <$> filter (\p -> fst p == dat) (dieAttributes d)

newtype Parser r = Parser { unParser :: () -> [String] -> ([String], Either String r) }

warn :: String -> Parser ()
warn msg = Parser $ \_ s ->
  let s' = msg : s
   in seq s' $ (s', Right ())

instance Functor Parser where
  fmap f mv = Parser $ \ctx s ->
    case unParser mv ctx s of
      (s', Left m) -> (s', Left m)
      (s', Right v) ->
        let fv = f v
            rfv = Right fv
         in seq fv $ seq rfv $ (s', rfv)

instance Applicative Parser where
  mf <*> mh = Parser $ \ctx s ->
    let (s1,ef) = unParser mf ctx s
        (s2,eh) = unParser mh ctx []
        mv = case (ef, eh) of
              (Right f, Right h) -> Right $! f h
              (Left m, _)        -> Left m
              (_, Left m)        -> Left m
        s3 = s1 ++ s2
     in (s3, mv)

  pure v = Parser $ \_ s ->
    let mv = Right v
     in seq v $ seq mv $ (s, mv)

instance Monad Parser where
  m >>= h = Parser $ \ctx s ->
    case unParser m ctx s of
      (s', Left msg) -> (s', Left msg)
      (s', Right v) -> unParser (h v) ctx s'
  return = pure
  fail msg = seq msg $ Parser $ \_ s -> (s, Left msg)

runParser :: Parser r -> ([String], Either String r)
runParser p = unParser p () []

runInContext :: (String -> String) -> Parser r -> Parser r
runInContext f m = Parser $ \ctx s ->
  let (warnings,mr) = unParser m ctx []
      warnings' = fmap f warnings ++ s
      v' = case mr of
             Left e -> Left (f e)
             Right r -> Right r
   in (warnings', v')

convertAttribute :: DW_AT
                 -> (DW_ATVAL -> Parser r)
                 -> DW_ATVAL -> Parser r
convertAttribute dat f v = runInContext h (f v)
  where h msg = "Could not interpret attribute " ++ show dat ++ " value " ++ show v ++ ": " ++ msg

checkTag :: DIE -> DW_TAG -> Parser ()
checkTag d tag =
  when (dieTag d /= tag) $ warn ("Expected " ++ show tag)

catchDIEError :: DIE -> DW_TAG -> Parser a -> Parser a
catchDIEError d tag m = checkTag d tag >> runInContext h m
  where h msg =
          "Error parsing " ++ show tag ++ ":\n" ++ unlines (("  " ++) <$> lines msg)

getSingleAttribute :: DIE -> DW_AT -> (DW_ATVAL -> Parser v) -> Parser v
getSingleAttribute d dat f =
  case getAttribute d dat of
    [] -> fail $ "Expected attribute " ++ show dat ++ " in " ++ show d ++ "."
    [v] -> convertAttribute dat f v
    _ -> fail $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

getMaybeAttribute :: DIE -> DW_AT -> (DW_ATVAL -> Parser v) -> Parser (Maybe v)
getMaybeAttribute d dat f =
  case getAttribute d dat of
    [] -> pure Nothing
    [v] -> Just <$> convertAttribute dat f v
    _ -> fail $ "Found multiple attributes for " ++ show dat ++ " in " ++ show d ++ "."

attributeAsBlob :: DW_ATVAL -> Parser BS.ByteString
attributeAsBlob (DW_ATVAL_BLOB b) = pure b
attributeAsBlob _ = fail "Could not interpret as Bool"


attributeAsBool :: DW_ATVAL -> Parser Bool
attributeAsBool (DW_ATVAL_BOOL b) = pure b
attributeAsBool _ = fail "Could not interpret as Bool"

attributeAsUInt :: DW_ATVAL -> Parser Word64
attributeAsUInt (DW_ATVAL_UINT u) = pure u
attributeAsUInt _ = fail "Could not interpret as UInt"

attributeAsDieID :: DW_ATVAL -> Parser DieID
attributeAsDieID (DW_ATVAL_REF r) = pure r
attributeAsDieID _ = fail "Could not interpret as DieID."

attributeAsString :: DW_ATVAL -> Parser String
attributeAsString (DW_ATVAL_STRING s) = pure s
attributeAsString _ = fail "Could not interpret as string."

lookupDIE :: Map DieID DIE -> DieID -> Parser DIE
lookupDIE m k =
  case Map.lookup k m of
    Just d -> pure d -- (dieRefsDIE d)
    Nothing -> fail "Could not find die."

attributeAsDIE :: Map DieID DIE -> DW_ATVAL -> Parser DIE
attributeAsDIE m v = lookupDIE m =<< attributeAsDieID v

maybeToEither :: String -> Maybe a -> Parser a
maybeToEither _ (Just r) = pure r
maybeToEither msg Nothing = fail msg

attributeAsLang :: DW_ATVAL -> Parser DW_LANG
attributeAsLang v = do
  u <- attributeAsUInt v
  maybeToEither "Could not parse lang" (get_dw_lang u)

checkAttributesKnown :: DIE -> Set DW_AT -> Parser ()
checkAttributesKnown d s = do
  let unknownAttrs = filter (\p -> Set.notMember (fst p) s) (dieAttributes d)
  when (null unknownAttrs == False) $ do
    warn $ show $
      text "Unknown attribute:" <$$>
      vcat (indent 2 . text . show <$> unknownAttrs)

checkChildrenKnown :: DIE -> Set DW_TAG -> Parser ()
checkChildrenKnown d s = do
  let unknownChildren = filter (\d' -> Set.notMember (dieTag d') s) (dieChildren d)
  when (null unknownChildren == False) $ do
    warn $ show $
      text "Unknown children:" <$$>
      vcat (indent 2 . text . show <$> unknownChildren)

hasTag :: DW_TAG -> DIE -> Bool
hasTag tag d = dieTag d == tag

parseGet :: BS.ByteString -> Get a -> Parser a
parseGet bs m =
  case pushEndOfInput (runGetIncremental m `pushChunk` bs) of
    Fail _ _ msg -> fail msg
    Partial _ -> fail "Unexpected partial"
    Done _ _ r -> do
      pure r

parseGetAll :: BS.ByteString -> Get a -> Parser a
parseGetAll bs m =
  case pushEndOfInput (runGetIncremental m `pushChunk` bs) of
    Fail _ _ msg -> fail msg
    Partial _ -> fail "Unexpected partial"
    Done remain _ r -> do
      unless (BS.null remain) $ fail "Did not consume all input."
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
-- DeclLoc

data DeclLoc = DeclLoc { locFile :: !FilePath
                       , locLine :: !Word64
                       }

instance Pretty DeclLoc where
  pretty loc =
    text "decl_file:  " <+> text (locFile loc) <$$>
    text "decl_line:  " <+> text (show (locLine loc))

instance Show DeclLoc where
  show = show . pretty

------------------------------------------------------------------------
-- DW_OP pretty printing

ppOp :: DW_OP -> Doc
ppOp (DW_OP_addr w) = text (showHex w "")
ppOp o = text (show o)

------------------------------------------------------------------------
-- Type

data Member tp = Member { memberName :: !String
                        , memberLoc  :: !DeclLoc
                        , memberType :: tp
                        }
  deriving (Show)

data Struct tp = Struct { structName     :: !String
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

data Typedef tp = Typedef { typedefName :: !String
                          , typedefLoc  :: !DeclLoc
                          , typedefType :: tp
                          }
  deriving (Show)

data BaseType = BaseTypeDef { baseSize     :: !Word64
                            , baseEncoding :: !DW_ATE
                            , baseName     :: !String
                            }
  deriving (Show)

data EnumDecl = EnumDecl { enumByteSize :: !Word64
                         , enumLoc      :: !DeclLoc
                         , enumChildren :: ![DIE]
                         }
  deriving (Show)

data TypeF tp
   = BaseType !BaseType
   | ConstTypeF tp
   | VolatileType tp
   | PointerType tp
   | UnknownPointerType !Word64
   | StructType !(Struct tp)
     -- ^ Denotes a C struct
   | UnionType !(UnionDecl tp)
     -- ^ Denotes a C union
   | EnumType !EnumDecl
   | TypedefType !(Typedef tp)
   | ArrayType tp ![DIE]
   | UnknownType !DIE

  deriving (Show)

structMembersLens :: Lens (Struct a) (Struct b) [Member a] [Member b]
structMembersLens = lens structMembers (\s v -> s { structMembers = v })

unionMembersLens :: Lens (UnionDecl a) (UnionDecl b) [Member a] [Member b]
unionMembersLens = lens unionMembers (\s v -> s { unionMembers = v })

memberTypeLens :: Lens (Member a) (Member b) a b
memberTypeLens = lens memberType (\s v -> s { memberType = v })

typedefTypeLens :: Lens (Typedef a) (Typedef b) a b
typedefTypeLens = lens typedefType (\s v -> s { typedefType = v })


traverseSubtypes :: Traversal (TypeF a) (TypeF b) a b
traverseSubtypes f tf =
  case tf of
    ConstTypeF tp -> ConstTypeF <$> f tp
    VolatileType tp -> VolatileType <$> f tp
    PointerType tp  -> PointerType <$> f tp
    UnknownPointerType w -> pure (UnknownPointerType w)
    StructType s -> StructType <$> (structMembersLens . traverse . memberTypeLens) f s
    UnionType  u -> UnionType  <$> (unionMembersLens . traverse . memberTypeLens) f u
    EnumType e -> pure (EnumType e)
    TypedefType tp -> TypedefType <$> typedefTypeLens f tp
    ArrayType etp d -> (`ArrayType` d) <$> f etp
    UnknownType d -> pure (UnknownType d)
    BaseType tp -> pure (BaseType tp)

parseMember :: V.Vector FilePath -> DIE -> Parser (Member DieID)
parseMember file_vec d = catchDIEError d DW_TAG_member $ do
 checkChildrenKnown d Set.empty
 name       <- getSingleAttribute d DW_AT_name       attributeAsString
 declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename file_vec)
 declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt
 tp         <- getSingleAttribute d DW_AT_type attributeAsDieID

 let declLoc = DeclLoc { locFile = declFile
                       , locLine = declLine
                       }
 pure $! Member { memberName = name
                , memberLoc  = declLoc
                , memberType = tp
                }

attributeAsBaseTypeEncoding :: DW_ATVAL -> Parser DW_ATE
attributeAsBaseTypeEncoding v = do
  u <- attributeAsUInt v
  case get_dw_ate u of
    Just r -> pure r
    Nothing -> fail $ "Could not parser attribute encoding 0x" ++ showHex u "."

parseTypeF :: V.Vector FilePath -> DIE -> Parser (TypeF DieID)
parseTypeF file_vec d =
  case dieTag d of
    DW_TAG_base_type -> do
      size <- getSingleAttribute d DW_AT_byte_size attributeAsUInt
      enc  <- getSingleAttribute d DW_AT_encoding  attributeAsBaseTypeEncoding
      name <- getSingleAttribute d DW_AT_name      attributeAsString

      let def = BaseTypeDef { baseSize = size
                            , baseEncoding = enc
                            , baseName = name
                            }
      checkChildrenKnown d Set.empty
      checkAttributesKnown d $ Set.fromList [ DW_AT_byte_size, DW_AT_encoding, DW_AT_name ]
      pure $! BaseType def
    DW_TAG_const_type -> do
      mtp <- getMaybeAttribute d DW_AT_type attributeAsDieID
      checkChildrenKnown d Set.empty
      case mtp of
        Just tp -> pure $! ConstTypeF tp
        Nothing -> pure $! UnknownType d
    DW_TAG_volatile_type -> do
      tp <- getSingleAttribute d DW_AT_type attributeAsDieID
      checkChildrenKnown d Set.empty
      pure $! VolatileType tp
    DW_TAG_pointer_type -> do
      mtp <- getMaybeAttribute d DW_AT_type attributeAsDieID
      checkChildrenKnown d Set.empty
      checkAttributesKnown d (Set.fromList [ DW_AT_type, DW_AT_byte_size ])
      case mtp of
        Just tp -> pure $! PointerType tp
        Nothing -> do
          w <- getSingleAttribute d DW_AT_byte_size attributeAsUInt
          pure $! UnknownPointerType w
    DW_TAG_structure_type -> do
      name       <- fromMaybe "" <$> getMaybeAttribute d DW_AT_name       attributeAsString
      byte_size  <- getSingleAttribute d DW_AT_byte_size  attributeAsUInt
      declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename file_vec)
      declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt

      members <- traverse (parseMember file_vec) (dieChildren d)

      let declLoc = DeclLoc { locFile = declFile
                            , locLine = declLine
                            }
      let struct = Struct { structName     = name
                          , structByteSize = byte_size
                          , structLoc      = declLoc
                          , structMembers  = members
                          }
      pure $! StructType struct
    DW_TAG_union_type -> do
      name       <- fromMaybe "" <$> getMaybeAttribute d DW_AT_name       attributeAsString
      byte_size  <- getSingleAttribute d DW_AT_byte_size  attributeAsUInt
      declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename file_vec)
      declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt

      members <- traverse (parseMember file_vec) (dieChildren d)

      let declLoc = DeclLoc { locFile = declFile
                            , locLine = declLine
                            }
      let u = UnionDecl { unionName     = name
                        , unionByteSize = byte_size
                        , unionLoc      = declLoc
                        , unionMembers  = members
                        }
      pure $! UnionType u
    DW_TAG_typedef -> do
      name       <- getSingleAttribute d DW_AT_name       attributeAsString
      declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename file_vec)
      declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt
      tp <- getSingleAttribute d DW_AT_type attributeAsDieID

      let declLoc = DeclLoc { locFile = declFile
                            , locLine = declLine
                            }
      let td = Typedef { typedefName = name
                       , typedefLoc  = declLoc
                       , typedefType = tp
                       }
      checkChildrenKnown d Set.empty
      pure $! TypedefType td
    DW_TAG_array_type -> do
      eltType <- getSingleAttribute d DW_AT_type attributeAsDieID
      pure $! ArrayType eltType (dieChildren d)
    DW_TAG_enumeration_type -> do
      byte_size  <- getSingleAttribute d DW_AT_byte_size  attributeAsUInt
      declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename file_vec)
      declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt
      let declLoc = DeclLoc { locFile = declFile
                            , locLine = declLine
                            }
      let e = EnumDecl { enumByteSize = byte_size
                       , enumLoc      = declLoc
                       , enumChildren = dieChildren d
                       }
      pure $! EnumType e
    DW_TAG_subroutine_type -> do
      fail $ "subroutine_type " ++ show d
    _ ->
      pure $! UnknownType d

parseTypeMap :: V.Vector FilePath -> [DIE] -> Parser (Map DieID Type)
parseTypeMap file_vec l = do
  let go d = (\tf -> (dieId d, tf)) <$> parseTypeF file_vec d
  resolveTypeMap <$> traverse go l

------------------------------------------------------------------------
-- Type

newtype Type = Type (TypeF Type)

ppType :: Type -> Doc
ppType (Type tf) =
  case tf of
    BaseType b -> text (baseName b)
    ConstTypeF x   -> text "const" <+> ppType x
    VolatileType x -> text "volatile" <+> ppType x
    PointerType x  -> text "pointer" <+> ppType x
    UnknownPointerType w -> text "upointer" <+> text (show w)
    StructType s -> text "struct" <+> text (structName s)
    UnionType  u -> text "union"  <+> text (unionName  u)
    EnumType e   -> text "enum" <+> text (show e)
    TypedefType d -> text "typedef" <+> text (typedefName d)
    ArrayType etp l -> text "array" <+> ppType etp <+> text (show l)
    UnknownType d -> text "unknown" <+> text (show d)

resolveTypeMap :: [(DieID, TypeF DieID)] -> Map DieID Type
resolveTypeMap m = r
  where r = Map.fromList
          [ (d, Type (tf & traverseSubtypes %~ g))
          | (d, tf) <- m
          ]

        g :: DieID -> Type
        g d = trace ("Eval " ++ show d) $
              fromMaybe (error $ "Could not find die ID " ++ show d) $
              Map.lookup d r


------------------------------------------------------------------------
-- Variable

data Variable = Variable { varName :: !String
                         , varDeclLoc :: !DeclLoc
                         , varType :: !Type
                         , varLocation :: !(Maybe DW_OP)
                         }

instance Pretty Variable where
  pretty v =
    text "name:    " <+> text (varName v) <$$>
    pretty (varDeclLoc v) <$$>
    text "type:    " <+> ppType (varType v) <$$>
    maybe (text "") (\o -> text "location:" <+> ppOp o) (varLocation v)

instance Show Variable where
   show = show . pretty

variableChildren :: Set DW_TAG
variableChildren =  Set.fromList
  [
  ]

variableAttributes :: Set DW_AT
variableAttributes = Set.fromList
  [ DW_AT_name
  , DW_AT_decl_file
  , DW_AT_decl_line
  , DW_AT_type
  , DW_AT_location
    -- Other
  , DW_AT_external
  , DW_AT_const_value
  , DW_AT_declaration
  ]

parseType :: Map DieID tp -> DieID -> Parser tp
parseType m k =
  case Map.lookup k m of
    Just v -> pure v
    Nothing -> fail $ "Could not resolve type with id " ++ show k ++ "."

parseVariable :: Reader -> V.Vector FilePath -> Map DieID Type -> DIE -> Parser Variable
parseVariable dr file_vec typeMap d = catchDIEError d DW_TAG_variable $ do
  let end = drEndianess dr
  let tgt = drTarget64 dr
  checkChildrenKnown   d variableChildren
  checkAttributesKnown d variableAttributes

  name       <- getSingleAttribute d DW_AT_name       attributeAsString
  declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename file_vec)
  declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt
  var_type   <- getSingleAttribute d DW_AT_type $ \val -> do
    parseType typeMap =<< attributeAsDieID val
  mloc       <- getMaybeAttribute  d DW_AT_location $ \v ->
      (`parseGetAll` getDW_OP end tgt) =<< attributeAsBlob v
  let declLoc = DeclLoc { locFile = declFile
                        , locLine = declLine
                        }
  pure $! Variable { varName     = name
                   , varDeclLoc  = declLoc
                   , varType     = var_type
                   , varLocation = mloc
                   }


------------------------------------------------------------------------
-- Subprogram


data SubprogramDef = SubprogramDef { subLowPC  :: !Word64
                                   , subHighPC :: !Word64
                                   , subFrameBase  :: !BS.ByteString
                                   , subGNUAllCallSites :: !(Maybe Bool)
                                   }

data Subprogram = Subprogram { subExternal   :: !Bool
                             , subName       :: !String
                             , subDeclLoc    :: !(Maybe DeclLoc)
                             , subPrototyped :: !Bool
                             , subDef        :: !(Maybe SubprogramDef)
                             , subChildren   :: ![DIE]
                             }

data InlinedSubprogram = InlinedSubprogram { isubExternal   :: !Bool
                                           , isubOrigin     :: !DIE
                                           , isubDef        :: !(Maybe SubprogramDef)
                                           , isubChildren   :: ![DIE]
                                           }

instance Show Subprogram where
  show = show . pretty

instance Pretty Subprogram where
  pretty sub =
    text "external:   " <+> text (show (subExternal sub)) <$$>
    text "name:       " <+> text (subName sub) <$$>
    loc_doc <$$>
    text "prototyped: " <+> text (show (subPrototyped sub)) <$$>
    def_doc <$$>
    text "children:" <$$>
    vcat (indent 2 . text . show <$> subChildren sub)
   where loc_doc =
           case subDeclLoc sub of
             Nothing -> text ""
             Just loc -> pretty loc
         def_doc = case subDef sub of
                     Nothing -> text ""
                     Just d ->
                       text "low_pc:     " <+> text (showHex (subLowPC d) "") <$$>
                       text "high_pc:    " <+> text (showHex (subHighPC d) "") <$$>
                       text "frame_base: " <+> text (show (subFrameBase d)) <$$>
                       text "GNU_all_call_sites: " <+> text (show (subGNUAllCallSites d))

subprogramChildren :: Set DW_TAG
subprogramChildren =  Set.fromList
  [ DW_TAG_formal_parameter
  , DW_TAG_user 0x89
  , DW_TAG_variable
  , DW_TAG_inlined_subroutine
  , DW_TAG_lexical_block
  , DW_TAG_union_type
  , DW_TAG_const_type
  ]

subprogramAttributes :: Set DW_AT
subprogramAttributes = Set.fromList
  [ DW_AT_external
  , DW_AT_name
  , DW_AT_decl_file
  , DW_AT_decl_line
  , DW_AT_prototyped
  , DW_AT_low_pc
  , DW_AT_high_pc
  , DW_AT_frame_base
  , DW_AT_sibling
  , DW_AT_GNU_all_call_sites
  , DW_AT_inline
    --  Unparsed results
  , DW_AT_declaration
  , DW_AT_type
  , DW_AT_artificial
  , DW_AT_abstract_origin
  , DW_AT_GNU_all_tail_call_sites
  ]

parseSubprogram :: V.Vector FilePath
                -> Map DieID DIE
                -> DIE
                -> Parser (Either InlinedSubprogram Subprogram)
parseSubprogram filenames m d = catchDIEError d DW_TAG_subprogram $ do
  checkChildrenKnown   d subprogramChildren
  ext        <- fromMaybe False <$> getMaybeAttribute d DW_AT_external   attributeAsBool

  decl       <- fromMaybe False <$> getMaybeAttribute d DW_AT_declaration attributeAsBool
  inl        <- fromMaybe DW_INL_not_inlined <$>
    getMaybeAttribute d DW_AT_inline (\v -> dw_inl <$> attributeAsUInt v)
  let inlined = case inl of
                  DW_INL_not_inlined          -> False
                  DW_INL_inlined              -> True
                  DW_INL_declared_not_inlined -> False
                  DW_INL_declared_inlined     -> True
  def <-
    if decl || inlined then
      pure Nothing
     else do
      lowPC      <- getSingleAttribute d DW_AT_low_pc     attributeAsUInt
      highPC     <- getSingleAttribute d DW_AT_high_pc    attributeAsUInt
      frameBase  <- getSingleAttribute d DW_AT_frame_base attributeAsBlob
      callSites  <- getMaybeAttribute d DW_AT_GNU_all_call_sites attributeAsBool
      let def = SubprogramDef { subLowPC     = lowPC
                              , subHighPC    = highPC
                              , subFrameBase = frameBase
                              , subGNUAllCallSites = callSites
                              }
      pure $! Just def

  checkAttributesKnown d subprogramAttributes

  mabstract_origin <- getMaybeAttribute d DW_AT_abstract_origin (attributeAsDIE m)
  case mabstract_origin of
    Nothing -> do
      name       <- getSingleAttribute d DW_AT_name       attributeAsString
      prototyped <- getSingleAttribute d DW_AT_prototyped attributeAsBool
      artificial <- fromMaybe False <$> getMaybeAttribute d DW_AT_artificial attributeAsBool
      mloc <-
        if artificial then do
          pure Nothing
         else do
          declFile   <- getSingleAttribute d DW_AT_decl_file  (attributeAsFilename filenames)
          declLine   <- getSingleAttribute d DW_AT_decl_line  attributeAsUInt
          let loc = DeclLoc { locFile = declFile
                            , locLine = declLine
                            }
          pure $! Just $! loc
      let sub = Subprogram { subExternal   = ext
                           , subName       = name
                           , subDeclLoc    = mloc
                           , subPrototyped = prototyped
                           , subDef        = def
                           , subChildren   = dieChildren d
                           }
      pure (Right sub)
    Just origin -> do
      let isub = InlinedSubprogram
            { isubExternal   = ext
            , isubOrigin     = origin
            , isubDef        = def
            , isubChildren   = dieChildren d
            }
      pure (Left isub)

------------------------------------------------------------------------
-- CompileUnit

data CompileUnit = CompileUnit { cuProducer :: String
                               , cuLanguage :: Maybe DW_LANG
                               , cuName     :: String
                               , cuCompDir  :: String
                               , cuGNUMacros :: !(Maybe Word64)
                               , cuSubprograms :: ![Subprogram]
                               , cuVariables   :: ![Variable]
                               }

instance Show CompileUnit where
  show = show . pretty

instance Pretty CompileUnit where
  pretty cu =
    text "producer:    " <+> text (cuProducer cu)         <$$>
    text "language:    " <+> text (show (cuLanguage cu))  <$$>
    text "name:        " <+> text (cuName cu)             <$$>
    text "comp_dir:    " <+> text (cuCompDir cu)          <$$>
    text "GNU_macros:  " <+> text (show (cuGNUMacros cu)) <$$>
    text "variables:   " <$$>
    vcat (indent 2 . pretty <$> cuVariables cu) <$$>
    text "subprograms: " <$$>
    vcat (indent 2 . pretty <$> cuSubprograms cu)

compileUnitChildren :: Set DW_TAG
compileUnitChildren = Set.fromList
  [ DW_TAG_subprogram
  , DW_TAG_variable
  , DW_TAG_subroutine_type

    -- Types
  , DW_TAG_base_type
  , DW_TAG_const_type
  , DW_TAG_volatile_type
  , DW_TAG_pointer_type
  , DW_TAG_structure_type
  , DW_TAG_union_type
  , DW_TAG_enumeration_type
  , DW_TAG_typedef
  , DW_TAG_array_type
  ]

compileUnitAttributes :: Set DW_AT
compileUnitAttributes = Set.fromList
  [ DW_AT_producer
  , DW_AT_language
  , DW_AT_name
  , DW_AT_comp_dir
  , DW_AT_stmt_list
  , DW_AT_GNU_macros
  , DW_AT_low_pc
  , DW_AT_high_pc
    -- Unparsed types
  , DW_AT_ranges
  ]

parseCompileUnit :: BS.ByteString
                    -- ^ .debug_line offset
                 -> (CUContext, DIE)
                 -> Parser CompileUnit
parseCompileUnit lines_bs (ctx,d) = catchDIEError d DW_TAG_compile_unit $ do
  let dr = cuReader ctx
  let end = drEndianess dr
  let tgt = drTarget64 dr
  checkChildrenKnown   d compileUnitChildren
  checkAttributesKnown d compileUnitAttributes
  prod      <- getSingleAttribute d DW_AT_producer   attributeAsString
  lang      <- getMaybeAttribute  d DW_AT_language   attributeAsLang
  name      <- getSingleAttribute d DW_AT_name       attributeAsString
  compDir   <- getSingleAttribute d DW_AT_comp_dir   attributeAsString
  -- Get offset into .debug_line for this compile units line number information
  mdebug_line_offset <- getMaybeAttribute  d DW_AT_stmt_list  attributeAsUInt
  _lowPC    <- getMaybeAttribute  d DW_AT_low_pc     attributeAsUInt
  _highPC   <- getMaybeAttribute  d DW_AT_high_pc    attributeAsUInt
  gnuMacros <- getMaybeAttribute  d DW_AT_GNU_macros attributeAsUInt
  (file_list, _lne) <-
    case mdebug_line_offset of
      Nothing ->
        pure ([], [])
      Just offset -> do
        when (fromIntegral offset > BS.length lines_bs) $ do
          fail "Illegal compile unit debug_line offset"
        let bs = BS.drop (fromIntegral offset) lines_bs
          in parseGet bs (getLNE end tgt)
  let idMap = Map.fromList [ (dieId d', d') | d' <- dieChildren d ]
  let file_vec = V.fromList file_list
  (_isub, subprograms) <- fmap partitionEithers $ traverse (parseSubprogram file_vec idMap) $
    filter (hasTag DW_TAG_subprogram) (dieChildren d)
  typeMap <- parseTypeMap file_vec (dieChildren d)
  variables <- traverse (parseVariable dr file_vec typeMap) $
    filter (hasTag DW_TAG_variable) (dieChildren d)
  pure $! CompileUnit { cuProducer  = prod
                      , cuLanguage  = lang
                      , cuName      = name
                      , cuCompDir   = compDir
                      , cuGNUMacros = gnuMacros
                      , cuSubprograms = subprograms
                      , cuVariables   = variables
                      }

------------------------------------------------------------------------
-- loadDwarf

tryGetElfSection :: String -> Elf v -> Parser BS.ByteString
tryGetElfSection nm e =
  case findSectionByName nm e of
    [s] -> pure $ elfSectionData s
    [] -> fail $ "Could not find " ++ show nm ++ " section."
    _  -> fail $ "Found multiple " ++ show nm ++ " sections."

loadDwarf :: Elf v -> ([String], Either String [CompileUnit])
loadDwarf e = runParser $ do
  let end =
        case elfData e of
          ELFDATA2LSB -> LittleEndian
          ELFDATA2MSB -> BigEndian
  debug_abbrev <- tryGetElfSection ".debug_abbrev" e
  debug_info   <- tryGetElfSection ".debug_info"   e
  debug_lines  <- tryGetElfSection ".debug_line"   e
  debug_str    <- tryGetElfSection ".debug_str"    e
  let sections = Sections { dsInfoSection   = debug_info
                          , dsAbbrevSection = debug_abbrev
                          , dsStrSection    = debug_str
                          }
  let (cuDies, _m) = parseInfo end sections
  traverse (parseCompileUnit debug_lines) cuDies

dwarfGlobals :: [CompileUnit] -> [Variable]
dwarfGlobals units = fmap snd (sortOn fst l)
  where l = [ (w,var)
            | cu <- units
            , var <- cuVariables cu
            , w <- maybeToList (varLocation var)
            ]
