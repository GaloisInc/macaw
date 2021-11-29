{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
-- | This module defines a concrete syntax parser for macaw, which is meant to
-- make it easy to persist analysis results and reuse them without recomputing
-- everything
--
-- The persisted artifact is a zip file with one file per function, plus a
-- manifest file that records metadata about the binary to enable the loader to
-- check to ensure that the loaded macaw IR actually matches the given binary.
module Data.Macaw.Syntax.Parser (
  parseDiscoveryFunInfo
  ) where

import           Control.Applicative ( (<|>) )
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import           GHC.TypeLits ( type (<=) )
import           Numeric.Natural ( Natural )
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC
import qualified Text.Megaparsec.Char.Lexer as TMCL

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Discovery.State as MDS
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Syntax.Atom
import qualified Data.Macaw.Syntax.SExpr as SExpr
import qualified Data.Macaw.Types as MT

-- | Identifiers are like scheme identifiers (i.e., start with an alphabetic
-- character, can contain alphanumeric characters plus dashes and underscores)
parseIdentifier :: SExpr.Parser arch ids T.Text
parseIdentifier = do
  c1 <- TMC.letterChar
  cs <- TM.many (TM.try TMC.alphaNumChar <|> TM.try (TMC.char '-') <|> TMC.char '_')
  return (T.pack (c1 : cs))

parseKeywordOrAtom :: SExpr.Parser arch ids Atom
parseKeywordOrAtom = do
  x <- parseIdentifier
  return $! maybe (AtomName (AtomText x)) Keyword (Map.lookup x keywords)

parseAddress :: SExpr.Parser arch ids Atom
parseAddress = Address <$> (TMC.string "0x" >> TMCL.hexadecimal)

parseNatural :: SExpr.Parser arch ids Atom
parseNatural = Natural_ <$> TMCL.decimal

parseRegister :: SExpr.Parser arch ids Atom
parseRegister = Register <$> (TMC.char '$' >> TMCL.decimal)

parseInteger :: SExpr.Parser arch ids Atom
parseInteger = TM.try (Integer_ <$> (TMC.char '+' >> TMCL.decimal))
               <|> (Integer_ <$> (TMC.char '-' >> TMCL.decimal))

parseString :: SExpr.Parser arch ids Atom
parseString = (String_ . T.pack) <$> (TMC.char '"' >> TM.manyTill TMCL.charLiteral (TMC.char '"'))

-- | Parse a single 'Atom'
--
-- Note that the order of these parsers matters a lot.  We have to parse
-- registers before general atoms, as they overlap
parseAtom :: SExpr.Parser arch ids Atom
parseAtom = TM.try parseRegister
        <|> TM.try parseKeywordOrAtom
        <|> TM.try parseNatural
        <|> TM.try parseInteger
        <|> TM.try parseAddress
        <|> parseString

parse
  :: (SExpr.Syntax Atom -> Either SExpr.MacawSyntaxError a)
  -> SExpr.Parser arch ids a
parse asSomething = do
  at <- SExpr.sexp parseAtom
  case asSomething at of
    Left err -> TM.customFailure err
    Right r -> return r

parseSExpr
  :: forall arch ids a
   . SExpr.Syntax Atom
  -> (SExpr.Syntax Atom -> Either SExpr.MacawSyntaxError a)
  -> SExpr.Parser arch ids a
parseSExpr sexp asSomething =
  case asSomething sexp of
    Left err -> TM.customFailure err
    Right r -> return r

data WidthRepr where
  WidthRepr :: (1 <= n) => PN.NatRepr n -> WidthRepr

-- | Attempt to convert a 'Natural' into a non-zero 'PN.NatRepr'
asWidthRepr :: Natural -> Maybe WidthRepr
asWidthRepr nat =
  case PN.mkNatRepr nat of
    Some nr
      | Right PN.LeqProof <- PN.isZeroOrGT1 nr -> Just (WidthRepr nr)
      | otherwise -> Nothing

asEndianness :: SExpr.Syntax Atom -> Either SExpr.MacawSyntaxError MM.Endianness
asEndianness at =
  case at of
    SExpr.A (Keyword BigEndian) -> Right MM.BigEndian
    SExpr.A (Keyword LittleEndian) -> Right MM.LittleEndian
    _ -> Left (SExpr.InvalidEndianness at)

asMemRepr :: SExpr.Syntax Atom -> Either SExpr.MacawSyntaxError (SomeTyped MC.MemRepr)
asMemRepr at =
  case at of
    SExpr.L [ SExpr.A (Keyword BVMemRepr), SExpr.A (Natural_ w), send ]
      | Just (WidthRepr nr) <- asWidthRepr w -> do
          end <- asEndianness send
          let nr8 = PN.natMultiply (PN.knownNat @8) nr
          -- This cannot fail because we already checked that @w@ is >= 1 above
          case PN.isZeroOrGT1 nr8 of
            Left _ -> error ("Impossible; w was >= 1, so w * 8 must be >= 1: " ++ show nr8)
            Right PN.LeqProof -> do
              let tyRep = MT.BVTypeRepr nr8
              return (SomeTyped tyRep (MC.BVMemRepr nr end))

data SomeTyped f where
  SomeTyped :: MT.TypeRepr tp -> f tp -> SomeTyped f

-- | Note: this does not yet handle relocatable values
asValue :: SExpr.Syntax Atom -> SExpr.Parser arch ids (SomeTyped (MC.Value arch ids))
asValue at = do
  as <- SExpr.getArchSyntax
  case at of
    SExpr.A (Keyword True_) -> return (SomeTyped MT.BoolTypeRepr (MC.BoolValue True))
    SExpr.A (Keyword False_) -> return (SomeTyped MT.BoolTypeRepr (MC.BoolValue False))
    SExpr.L [SExpr.A (Keyword BV), SExpr.A (Natural_ w), SExpr.A (Integer_ i)]
      | Just (WidthRepr nr) <- asWidthRepr w -> return (SomeTyped (MT.BVTypeRepr nr) (MC.BVValue nr i))
      | otherwise -> TM.customFailure SExpr.InvalidZeroWidthBV
    SExpr.A (Register rnum) -> do
      -- This generates an 'MC.AssignedValue'
      Some val <- SExpr.valueForRegisterNumber rnum
      return (SomeTyped (MT.typeRepr val) val)
    SExpr.A (AtomName aname)
      | Just (Some reg) <- SExpr.asArchRegister as aname -> return (SomeTyped (MT.typeRepr reg) (MC.Initial reg))
    _ -> TM.customFailure (SExpr.InvalidValue at)

binaryBVApp
  :: Keyword
  -> (forall n . (1 <= n) => PN.NatRepr n -> MC.Value arch ids (MT.BVType n) -> MC.Value arch ids (MT.BVType n) -> MC.App (MC.Value arch ids) (MT.BVType n))
  -> SExpr.Syntax Atom
  -> SExpr.Syntax Atom
  -> SExpr.Parser arch ids (SomeTyped (MC.App (MC.Value arch ids)))
binaryBVApp kw con lhs rhs = do
  SomeTyped lrep lhs' <- asValue lhs
  SomeTyped rrep rhs' <- asValue rhs
  case (PC.testEquality lrep rrep, lrep) of
    (Just PC.Refl, MT.BVTypeRepr nr) -> return (SomeTyped lrep (con nr lhs' rhs'))
    _ -> TM.customFailure (SExpr.InvalidAppArguments kw)

unaryBVApp
  :: Keyword
  -> (forall n . (1 <= n) => PN.NatRepr n -> MC.Value arch ids (MT.BVType n) -> MC.App (MC.Value arch ids) (MT.BVType n))
  -> SExpr.Syntax Atom
  -> SExpr.Parser arch ids (SomeTyped (MC.App (MC.Value arch ids)))
unaryBVApp kw con op = do
  SomeTyped rep op' <- asValue op
  case rep of
    MT.BVTypeRepr nr -> return (SomeTyped rep (con nr op'))
    _ -> TM.customFailure (SExpr.InvalidAppArguments kw)

binaryBoolApp
  :: Keyword
  -> MT.TypeRepr tp
  -> (MC.Value arch ids tp -> MC.Value arch ids tp -> MC.App (MC.Value arch ids) tp)
  -> SExpr.Syntax Atom
  -> SExpr.Syntax Atom
  -> SExpr.Parser arch ids (SomeTyped (MC.App (MC.Value arch ids)))
binaryBoolApp kw tp con lhs rhs = do
  SomeTyped lrep lhs' <- asValue lhs
  SomeTyped rrep rhs' <- asValue rhs
  case (PC.testEquality tp lrep, PC.testEquality tp rrep) of
    (Just PC.Refl, Just PC.Refl) -> return (SomeTyped tp (con lhs' rhs'))
    _ -> TM.customFailure (SExpr.InvalidAppArguments kw)

asApp :: SExpr.Syntax Atom -> SExpr.Parser arch ids (SomeTyped (MC.App (MC.Value arch ids)))
asApp a =
  case a of
    SExpr.L [ SExpr.A (Keyword BVAdd), lhs, rhs ] ->
      binaryBVApp BVAdd MC.BVAdd lhs rhs
    SExpr.L [ SExpr.A (Keyword BVSub), lhs, rhs ] ->
      binaryBVApp BVSub MC.BVSub lhs rhs
    SExpr.L [ SExpr.A (Keyword BVMul), lhs, rhs ] ->
      binaryBVApp BVMul MC.BVMul lhs rhs
    -- SExpr.L [ SExpr.A (Keyword BVAdc), lhs, rhs ] ->
    --   binaryBVApp BVAdc MC.BVAdc lhs rhs
    -- SExpr.L [ SExpr.A (Keyword BVSbb), lhs, rhs ] ->
    --   binaryBVApp BVSbb MC.BVSbb lhs rhs
    SExpr.L [ SExpr.A (Keyword BVAnd), lhs, rhs ] ->
      binaryBVApp BVAnd MC.BVAnd lhs rhs
    SExpr.L [ SExpr.A (Keyword BVOr), lhs, rhs ] ->
      binaryBVApp BVOr MC.BVOr lhs rhs
    SExpr.L [ SExpr.A (Keyword BVXor), lhs, rhs ] ->
      binaryBVApp BVXor MC.BVXor lhs rhs
    SExpr.L [ SExpr.A (Keyword BVShl), lhs, rhs ] ->
      binaryBVApp BVShl MC.BVShl lhs rhs
    SExpr.L [ SExpr.A (Keyword BVShr), lhs, rhs ] ->
      binaryBVApp BVShr MC.BVShr lhs rhs
    SExpr.L [ SExpr.A (Keyword BVSar), lhs, rhs ] ->
      binaryBVApp BVSar MC.BVSar lhs rhs
    SExpr.L [ SExpr.A (Keyword PopCount), op ] ->
      unaryBVApp PopCount MC.PopCount op
    SExpr.L [ SExpr.A (Keyword Bsf), op ] ->
      unaryBVApp Bsf MC.Bsf op
    SExpr.L [ SExpr.A (Keyword Bsr), op ] ->
      unaryBVApp Bsr MC.Bsr op
    SExpr.L [ SExpr.A (Keyword BVComplement), op ] ->
      unaryBVApp BVComplement MC.BVComplement op
    SExpr.L [ SExpr.A (Keyword Mux), cond, t, f ] -> do
      SomeTyped crep cond' <- asValue cond
      SomeTyped trep t' <- asValue t
      SomeTyped frep f' <- asValue f
      case (PC.testEquality trep frep, crep) of
        (Just PC.Refl, MT.BoolTypeRepr) -> return (SomeTyped trep (MC.Mux trep cond' t' f'))
        _ -> TM.customFailure (SExpr.InvalidAppArguments Mux)
    SExpr.L [ SExpr.A (Keyword Eq_), lhs, rhs ] -> do
      SomeTyped lrep lhs' <- asValue lhs
      SomeTyped rrep rhs' <- asValue rhs
      case PC.testEquality lrep rrep of
        Just PC.Refl -> return (SomeTyped MT.BoolTypeRepr (MC.Eq lhs' rhs'))
        _ -> TM.customFailure (SExpr.InvalidAppArguments Eq_)
    SExpr.L [ SExpr.A (Keyword And_), lhs, rhs ] ->
      binaryBoolApp And_ MT.BoolTypeRepr MC.AndApp lhs rhs
    SExpr.L [ SExpr.A (Keyword Or_), lhs, rhs ] ->
      binaryBoolApp Or_ MT.BoolTypeRepr MC.OrApp lhs rhs
    SExpr.L [ SExpr.A (Keyword Xor_), lhs, rhs ] ->
      binaryBoolApp Xor_ MT.BoolTypeRepr MC.XorApp lhs rhs
    SExpr.L [ SExpr.A (Keyword Not_), op ] -> do
      SomeTyped rep op' <- asValue op
      case rep of
        MT.BoolTypeRepr -> return (SomeTyped MT.BoolTypeRepr (MC.NotApp op'))
        _ -> TM.customFailure (SExpr.InvalidAppArguments Not_)


-- | Parse a single type as a 'MT.TypeRepr'
--
-- The type forms are:
--
--  * @Bool@
--  * @(BV n)@
--  * @(Vec n ty)@
asTypeRepr :: SExpr.Syntax Atom -> Either SExpr.MacawSyntaxError (Some MT.TypeRepr)
asTypeRepr at =
  case at of
    SExpr.A (Keyword Bool_) -> Right (Some MT.BoolTypeRepr)
    SExpr.L [SExpr.A (Keyword BV_), SExpr.A (Natural_ w)]
      | Just (WidthRepr nr) <- asWidthRepr w -> Right (Some (MT.BVTypeRepr nr))
      | otherwise -> Left SExpr.InvalidZeroWidthBV
    SExpr.L [SExpr.A (Keyword Vec_), SExpr.A (Natural_ w), mty] ->
      case PN.mkNatRepr w of
        Some nr ->
          -- Note that zero-width vectors are technically allowed
          case asTypeRepr mty of
            Right (Some ty) -> Right (Some (MT.VecTypeRepr nr ty))
            Left _errs -> Left (SExpr.InvalidVectorPayload mty)
    _ -> Left (SExpr.InvalidType at)

-- | Parse the right-hand side of an assignment
--
-- Note that it is important that the EvalApp case is last, as there are many
-- syntactic forms that we might need to dispatch to.
asRHS
  :: forall arch ids
   . SExpr.Syntax Atom
  -> SExpr.Parser arch ids (Some (MC.AssignRhs arch (MC.Value arch ids)))
asRHS a =
  case a of
    SExpr.L [ SExpr.A (Keyword Undefined), srep ] -> do
      Some rep <- parseSExpr srep asTypeRepr
      return (Some (MC.SetUndefined rep))
    SExpr.L [ SExpr.A (Keyword ReadMemory), saddr, smemRepr ] -> do
      SomeTyped addrTp addr <- asValue saddr
      SomeTyped _rep memRepr <- parseSExpr smemRepr asMemRepr

      memWidth <- SExpr.archMemWidth
      let addrRepr = MT.BVTypeRepr memWidth

      case PC.testEquality addrTp addrRepr of
        Just PC.Refl -> return (Some (MC.ReadMem addr memRepr))
        Nothing -> TM.customFailure (SExpr.InvalidAddressWidth a)
    _ -> do
      SomeTyped _tp app <- asApp a
      return (Some (MC.EvalApp app))

-- | Forms:
--
--  * @(comment "msg")@
--  * @(instruction-start addr decoded-asm-text)@
--  * @(write-memory addr mem-rep value)@
--  * @(cond-write-memory cond addr mem-rep value)@
--  * @(reg := rhs)@
parseStmt :: forall arch ids . SExpr.Parser arch ids (MC.Stmt arch ids)
parseStmt = do
  at <- SExpr.sexp parseAtom
  case at of
    SExpr.L [ SExpr.A (Keyword Comment), SExpr.A (String_ txt) ] ->
      return (MC.Comment txt)
    SExpr.L [ SExpr.A (Keyword InstructionStart), SExpr.A (Address addr), SExpr.A (String_ txt) ] ->
      return (MC.InstructionStart (MM.memWord (fromIntegral addr)) txt)
    SExpr.L [ SExpr.A (Keyword WriteMemory), stargetAddr, smemRepr, svalue ] -> do
      SomeTyped addrTy addr <- asValue stargetAddr
      SomeTyped vtp value <- asValue svalue
      SomeTyped mtp memRepr <- parseSExpr smemRepr asMemRepr
      memWidth <- SExpr.archMemWidth
      let addrRepr = MT.BVTypeRepr memWidth
      case (PC.testEquality vtp mtp, PC.testEquality addrTy addrRepr) of
        (Just PC.Refl, Just PC.Refl) -> do
          return (MC.WriteMem addr memRepr value)
          -- FIXME: Make a more-specific error
        _ -> TM.customFailure (SExpr.InvalidStatement at)
    SExpr.L [ SExpr.A (Keyword CondWriteMemory), scond, stargetAddr, smemRepr, svalue ] -> do
      SomeTyped condTy cond <- asValue scond
      SomeTyped addrTy addr <- asValue stargetAddr
      SomeTyped vtp value <- asValue svalue
      SomeTyped mtp memRepr <- parseSExpr smemRepr asMemRepr
      memWidth <- SExpr.archMemWidth
      let addrRepr = MT.BVTypeRepr memWidth
      case (PC.testEquality vtp mtp, PC.testEquality addrTy addrRepr, PC.testEquality condTy MT.BoolTypeRepr) of
        (Just PC.Refl, Just PC.Refl, Just PC.Refl) -> do
          return (MC.CondWriteMem cond addr memRepr value)
          -- FIXME: Make a more-specific error
        _ -> TM.customFailure (SExpr.InvalidStatement at)
    SExpr.L [ SExpr.A (Register r), SExpr.A (Keyword Assign), srhs ] -> do
      Some rhs <- asRHS srhs
      Some asgn <- SExpr.defineRegister r rhs
      return (MC.AssignStmt asgn)
    _ -> TM.customFailure (SExpr.InvalidStatement at)

parseBlock :: SExpr.Parser arch ids (Parsed.ParsedBlock arch ids)
parseBlock = do

  stmts <- TM.many parseStmt

  return Parsed.ParsedBlock { Parsed.pblockAddr = undefined
                            , Parsed.pblockPrecond = undefined
                            , Parsed.blockSize = undefined
                            , Parsed.blockReason = undefined
                            , Parsed.blockAbstractState = undefined
                            , Parsed.blockJumpBounds = undefined
                            , Parsed.pblockStmts = stmts
                            , Parsed.pblockTermStmt = undefined
                            }

parseFunction :: SExpr.Parser arch ids (Some (MD.DiscoveryFunInfo arch))
parseFunction = do

  blocks <- TM.many parseBlock

  let dfi = MDS.DiscoveryFunInfo { MDS.discoveredFunReason = undefined
                                 , MDS.discoveredFunAddr = undefined
                                 , MDS.discoveredFunSymbol = undefined
                                 , MDS._parsedBlocks = Map.fromList [ (Parsed.pblockAddr pb, pb)
                                                                    | pb <- blocks
                                                                    ]
                                 , MDS.discoveredClassifyFailureResolutions = undefined
                                 }
  return (Some dfi)

parseDiscoveryFunInfo
  :: (MC.ArchConstraints arch)
  => SExpr.ArchSyntax arch
  -- ^ Architecture-specific parsers
  -> MM.Memory (MC.ArchAddrWidth arch)
  -- ^ The memory of the binary we are loading results for
  -> BS.ByteString
  -- ^ The bytes of the persisted file
  -> Either SExpr.MacawParseError (Some (MD.DiscoveryFunInfo arch))
parseDiscoveryFunInfo as mem bytes = SExpr.runParser as mem bytes parseFunction
