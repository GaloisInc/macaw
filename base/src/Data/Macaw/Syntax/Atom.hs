{-# LANGUAGE OverloadedStrings #-}
-- | The atoms of the concrete syntax for macaw
module Data.Macaw.Syntax.Atom (
    Keyword(..)
  , keywords
  , AtomName(..)
  , Atom(..)
  )
  where

import qualified Data.Map.Strict as Map
import qualified Data.Text as T
import           Numeric.Natural ( Natural )

-- | Macaw syntax keywords
--
-- These are the keywords for the *base* macaw IR (i.e., without
-- architecture-specific extensions).  The architecture-specific operations are
-- parsed as 'AtomName's initially and resolved by architecture-specific parsers
-- at the atom level.
data Keyword = BVAdd
             | BVSub
             | BVMul
             | BVAdc
             | BVSbb
             | BVAnd
             | BVOr
             | BVXor
             | BVShl
             | BVShr
             | BVSar
             | PopCount
             | Bsf
             | Bsr
             | BVComplement
             | Mux
             | Lt
             | Le
             | Sle
             | Slt
             -- Syntax
             | Assign
             -- Statements
             | Comment
             | InstructionStart
             | WriteMemory
             | CondWriteMemory
             -- Expressions
             | ReadMemory
             -- Boolean operations
             | Eq_
             | Not_
             | And_
             | Or_
             | Xor_
             -- Endianness
             | BigEndian
             | LittleEndian
             -- MemRepr
             | BVMemRepr
             -- Types
             | Bool_
             | BV_
             | Float_
             | Tuple_
             | Vec_
             -- Values
             | True_
             | False_
             | BV
             | Undefined
  deriving (Eq, Ord, Show)

-- | Uninterpreted atoms
newtype AtomName = AtomText T.Text
  deriving (Eq, Ord, Show)

data Atom = Keyword !Keyword     -- ^ Keywords include all of the built-in expressions and operators
          | AtomName !AtomName   -- ^ Non-keyword syntax atoms (to be interpreted at parse time)
          | Register !Natural    -- ^ A numbered local register (e.g., @r12@)
          | Address !Natural     -- ^ An arbitrary address rendered in hex ('ArchAddrWord' or 'SegoffAddr')
          | Integer_ !Integer    -- ^ Literal integers
          | Natural_ !Natural    -- ^ Literal naturals
          | String_ !T.Text      -- ^ Literal strings
  deriving (Eq, Ord, Show)

keywords :: Map.Map T.Text Keyword
keywords = Map.fromList [ ("bv-add", BVAdd)
                        , ("bv-sub", BVSub)
                        , ("bv-mul", BVMul)
                        , ("bv-adc", BVAdc)
                        , ("bv-sbb", BVSbb)
                        , ("bv-and", BVAnd)
                        , ("bv-or", BVOr)
                        , ("bv-xor", BVXor)
                        , ("bv-shl", BVShl)
                        , ("bv-shr", BVShr)
                        , ("bv-sar", BVSar)
                        , ("bv-complement", BVComplement)
                        , ("popcount", PopCount)
                        , ("bit-scan-forward", Bsf)
                        , ("bit-scan-reverse", Bsr)
                        , ("mux", Mux)
                        , ("eq", Eq_)
                        , ("<", Lt)
                        , ("<=", Le)
                        , ("<$", Slt)
                        , ("<=$", Sle)
                        , ("not", Not_)
                        , ("and", And_)
                        , ("or", Or_)
                        , ("xor", Xor_)
                        , ("Bool", Bool_)
                        , ("BV", BV_)
                        , ("Float", Float_)
                        , ("Tuple", Tuple_)
                        , ("Vec", Vec_)
                        , ("true", True_)
                        , ("false", False_)
                        , ("bv", BV)
                        , ("undefined", Undefined)
                        , ("read-memory", ReadMemory)
                        , (":=", Assign)
                        , ("comment", Comment)
                        , ("instruction-start", InstructionStart)
                        , ("write-memory", WriteMemory)
                        , ("cond-write-memory", CondWriteMemory)
                        , ("big-endian", BigEndian)
                        , ("little-endian", LittleEndian)
                        , ("bv-mem", BVMemRepr)
                        ]
