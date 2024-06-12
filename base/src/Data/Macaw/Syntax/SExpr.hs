{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.Syntax.SExpr (
    Position(..)
  , Positioned(..)
  , Syntax(..)
  , Datum(..)
  , Layer(..)
  , Parser
  , runParser
  , freshNonce
  , MacawParseError(..)
  , MacawSyntaxError(..)
  , memory
  , archMemWidth
  , valueForRegisterNumber
  , defineRegister
  , ArchSyntax(..)
  , getArchSyntax
  , Syntactic(..)
  , pattern L
  , pattern A
  , sexp
  , lexeme
  , symbol
  , syntaxPos
  , withPosFrom
  ) where

import           Control.Applicative ( empty, (<|>), Alternative )
import           Control.Monad ( MonadPlus )
import qualified Control.Monad.RWS as RWS
import qualified Control.Monad.Reader as CMR
import           Control.Monad.ST ( ST )
import qualified Control.Monad.State as CMS
import           Control.Monad.Trans ( lift )
import qualified Data.ByteString as BS
import qualified Data.Map as Map
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import           Numeric.Natural ( Natural )
import qualified Text.Megaparsec as TM
import qualified Text.Megaparsec.Char as TMC
import qualified Text.Megaparsec.Char.Lexer as TMCL

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Syntax.Atom ( Atom, AtomName, Keyword )
import qualified Data.Macaw.Types as MT

data Position = Position { file :: FilePath, line :: {-# UNPACK #-} !TM.Pos, column :: {-# UNPACK #-} !TM.Pos }
  deriving (Eq, Ord, Show)

data Positioned a = Positioned { position :: {-# UNPACK #-} !Position, positioned :: !a }
  deriving (Eq, Functor, Ord, Show)

data Layer f a = List [f a] | Atom !a
  deriving (Show, Functor, Eq, Ord)

newtype Syntax a = Syntax { unSyntax :: Positioned (Layer Syntax a) }
  deriving (Show, Functor, Eq, Ord)

newtype Datum a = Datum { unDatum :: Layer Datum a }
  deriving (Show, Functor, Eq)

class Syntactic a b | a -> b where
  syntaxE :: a -> Layer Syntax b

instance Syntactic (Layer Syntax a) a where
  syntaxE = id

instance Syntactic (Syntax a) a where
  syntaxE = positioned . unSyntax

pattern A :: Syntactic a b => b -> a
pattern A x <- (syntaxE -> Atom x)

pattern L :: Syntactic a b => [Syntax b] -> a
pattern L xs <- (syntaxE -> List xs)

syntaxPos :: Syntax a -> Position
syntaxPos = position . unSyntax

withPosFrom :: Syntax a -> b -> Positioned b
withPosFrom stx x = Positioned (syntaxPos stx) x

-- | Low-level syntax errors embedded in megaparsec parse errors
data MacawSyntaxError where
  InvalidZeroWidthBV :: MacawSyntaxError
  InvalidVectorPayload :: Syntax Atom -> MacawSyntaxError
  InvalidType :: Syntax Atom -> MacawSyntaxError
  InvalidStatement :: Syntax Atom -> MacawSyntaxError
  InvalidEndianness :: Syntax Atom -> MacawSyntaxError
  MissingRegisterDefinition :: Natural -> MacawSyntaxError
  DuplicateRegisterDefinition :: Natural -> MacawSyntaxError
  InvalidAddressWidth :: Syntax Atom -> MacawSyntaxError
  InvalidValue :: Syntax Atom -> MacawSyntaxError
  InvalidAppArguments :: Keyword -> MacawSyntaxError

deriving instance Eq MacawSyntaxError
deriving instance Ord MacawSyntaxError

data ArchSyntax arch =
  ArchSyntax { asArchRegister :: AtomName -> Maybe (Some (MC.ArchReg arch))
             }

data ParserContext arch ids =
  ParserContext { memory :: MM.Memory (MC.ArchAddrWidth arch)
                , nonceGen :: PN.NonceGenerator (ST ids) ids
                , archSyntax :: ArchSyntax arch
                }

data ParserState arch ids =
  ParserState { idMap :: Map.Map Natural (Some (MC.Assignment arch ids))
              }

newtype ParserM arch ids a = ParserM { runParserM :: TM.ParsecT MacawSyntaxError T.Text (RWS.RWST (ParserContext arch ids) () (ParserState arch ids) (ST ids)) a }
  deriving ( Functor
           , Applicative
           , Alternative
           , Monad
           , MonadPlus
           , TM.MonadParsec MacawSyntaxError T.Text
           , CMR.MonadReader (ParserContext arch ids)
           , CMS.MonadState (ParserState arch ids)
           )

type Parser arch ids a = (MC.ArchConstraints arch) => ParserM arch ids a

liftST :: ST ids a -> Parser arch ids a
liftST = ParserM . lift . lift

freshNonce :: forall arch ids (tp :: MT.Type) . Parser arch ids (PN.Nonce ids tp)
freshNonce = do
  ng <- CMR.asks nonceGen
  liftST $ PN.freshNonce ng

getArchSyntax :: Parser arch ids (ArchSyntax arch)
getArchSyntax = CMR.asks archSyntax

-- | Look up the value corresponding to a register number in the current
-- function; note that this assumes that definitions precede uses (and throws a
-- parse error if that is not true)
valueForRegisterNumber :: Natural -> Parser arch ids (Some (MC.Value arch ids))
valueForRegisterNumber rnum = do
  ids <- CMS.gets idMap
  case Map.lookup rnum ids of
    Just (Some asgn) -> return (Some (MC.AssignedValue asgn))
    Nothing -> TM.customFailure (MissingRegisterDefinition rnum)

-- | Define a new register to a value
--
-- This corresponds to the 'MC.AssignStmt' form
defineRegister
  :: forall arch ids (tp :: MT.Type)
   . Natural
  -> MC.AssignRhs arch (MC.Value arch ids) tp
  -> Parser arch ids (Some (MC.Assignment arch ids))
defineRegister rnum rhs = do
  ids <- CMS.gets idMap
  case Map.lookup rnum ids of
    Just _ -> TM.customFailure (DuplicateRegisterDefinition rnum)
    Nothing -> do
      rnonce <- freshNonce @arch @ids @tp
      let asgn = MC.Assignment (MC.AssignId rnonce) rhs
      CMS.modify' $ \s -> s { idMap = Map.insert rnum (Some asgn) (idMap s) }
      return (Some asgn)

archMemWidth :: Parser arch ids (PN.NatRepr (MC.ArchAddrWidth arch))
archMemWidth = CMR.asks (MM.memWidth . memory)

-- | Top-level parse errors returned by the parser
--
-- This includes megaparsec parse errors (see 'MacawSyntaxError')
data MacawParseError where
  InvalidUTF8 :: TEE.UnicodeException -> BS.ByteString -> MacawParseError
  ParseError :: TM.ParseErrorBundle T.Text MacawSyntaxError -> MacawParseError

runParser
  :: ArchSyntax arch
  -> MM.Memory (MC.ArchAddrWidth arch)
  -> BS.ByteString
  -> (forall ids . ParserM arch ids a)
  -> Either MacawParseError a
runParser as mem bytes p = PN.runSTNonceGenerator $ \ng -> do
  case TE.decodeUtf8' bytes of
    Left decodeErr -> return (Left (InvalidUTF8 decodeErr bytes))
    Right txt -> do
      let ctx = ParserContext { memory = mem
                              , nonceGen = ng
                              , archSyntax = as
                              }
      let st0 = ParserState { idMap = mempty }
      (res, _) <- RWS.evalRWST (TM.runParserT (runParserM p) "<bytes>" txt) ctx st0
      case res of
        Left err -> return (Left (ParseError err))
        Right a -> return (Right a)

-- | There are no comments supported in the macaw concrete syntax for now
skipWhitespace :: Parser arch ids ()
skipWhitespace = TMCL.space TMC.space1 empty empty

lexeme :: Parser arch ids a -> Parser arch ids a
lexeme = TMCL.lexeme skipWhitespace

withPos :: Parser arch ids a -> Parser arch ids (Positioned a)
withPos p = do
  TM.SourcePos fl ln col <- TM.getSourcePos
  let loc = Position fl ln col
  res <- p
  return $! Positioned { position = loc
                       , positioned = res
                       }

symbol :: T.Text -> Parser arch ids T.Text
symbol = TMCL.symbol skipWhitespace

list :: Parser arch ids (Syntax a) -> Parser arch ids (Syntax a)
list p = do
  Positioned loc _ <- withPos (symbol "(")
  xs <- TM.many p
  _ <- lexeme (symbol ")")
  return $! Syntax (Positioned loc (List xs))

sexp :: Parser arch ids a -> Parser arch ids (Syntax a)
sexp atom =
  (Syntax . fmap Atom <$> lexeme (withPos atom)) <|>
  list (sexp atom)
