{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Macaw.PPC.Semantics.TH
  ( genExecInstruction
  ) where

import Language.Haskell.TH

import qualified Data.Parameterized.Map as Map
import qualified Lang.Crucible.Solver.SimpleBuilder as S
import qualified Lang.Crucible.Solver.SimpleBackend as S
import qualified Lang.Crucible.BaseTypes as S

import qualified Dismantle.PPC as D
import           SemMC.Formula
import qualified SemMC.Architecture as A
import Data.Macaw.CFG.Core
import qualified Data.Macaw.Types as M

import Data.Parameterized.NatRepr (knownNat)

import Data.Macaw.PPC.Generator

-- generate a different case for each key/value pair in the map
genExecInstruction :: Map.MapF (A.Opcode arch (A.Operand arch)) (ParameterizedFormula sym arch)
                   -> Q Exp
genExecInstruction _ = [| undefined |]

-- SemMC.Formula: instantiateFormula

type Sym t = S.SimpleBackend t

-- I'm trying to convert Crucible SymExpr's to Macaw expressions. I'm not sure what
-- data type to use.

type family FromCrucibleBaseType (btp :: S.BaseType) :: M.Type where
  FromCrucibleBaseType (S.BaseBVType w) = M.BVType w

eltToExpr :: S.Elt t ctp -> Expr ppc ids (FromCrucibleBaseType ctp)
eltToExpr (S.BVElt w val loc) = ValueExpr (BVValue w val)
eltToExpr (S.AppElt appElt) = undefined $ S.appEltApp appElt

-- | Given a location to modify and a crucible formula, construct a PPCGenerator that
-- will modify the location by the function encoded in the formula.
interpretFormula :: A.Location ppc tp -> S.SymExpr (Sym t) tp -> PPCGenerator ppc s ()
interpretFormula loc elt = undefined -- do { addAssignment (eltToAssignRhs elt) ; return () }
