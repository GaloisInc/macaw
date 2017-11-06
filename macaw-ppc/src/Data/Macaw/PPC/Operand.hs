{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- | Tools for extracting Macaw values from instruction operands
module Data.Macaw.PPC.Operand (
  ExtractValue,
  extractValue,
  ToPPCReg,
  toPPCReg
  ) where

import           GHC.TypeLits
import           Data.Int ( Int16 )
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Macaw.CFG.Core as MC
import           Data.Macaw.Types
import qualified Data.Word.Indexed as W
import qualified Data.Int.Indexed as I
import qualified Dismantle.PPC as D

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import qualified Data.Macaw.PPC.PPCReg as R
import qualified Data.Macaw.PPC.Generator as G

class ExtractValue arch a tp | arch a -> tp where
  extractValue :: a -> G.PPCGenerator arch ids s (MC.Value arch ids tp)

instance ExtractValue arch Bool BoolType where
  extractValue = return . MC.BoolValue

instance ExtractValue PPC32.PPC D.GPR (BVType 32) where
  extractValue gpr = G.getRegValue (R.PPC_GP gpr)

instance ExtractValue PPC32.PPC (Maybe D.GPR) (BVType 32) where
  extractValue mgpr =
    case mgpr of
      Just gpr -> extractValue gpr
      Nothing -> return $ MC.BVValue NR.knownNat 0

instance ExtractValue PPC64.PPC D.GPR (BVType 64) where
  extractValue gpr = G.getRegValue (R.PPC_GP gpr)

instance ExtractValue PPC64.PPC (Maybe D.GPR) (BVType 64) where
  extractValue mgpr =
    case mgpr of
      Just gpr -> extractValue gpr
      Nothing -> return $ MC.BVValue NR.knownNat 0

instance ExtractValue ppc D.FR (BVType 128) where
  extractValue fr = G.getRegValue (R.PPC_FR fr)

instance ExtractValue arch D.AbsBranchTarget (BVType 24) where
  extractValue (D.ABT w) = return $ MC.BVValue NR.knownNat (fromIntegral w)

instance ExtractValue arch D.CondBranchTarget (BVType 14) where
  extractValue (D.CBT i) = return $ MC.BVValue NR.knownNat (fromIntegral i)

instance ExtractValue arch D.AbsCondBranchTarget (BVType 14) where
  extractValue (D.ACBT w) = return $ MC.BVValue NR.knownNat (fromIntegral w)

instance ExtractValue arch D.BranchTarget (BVType 24) where
  extractValue (D.BT i) = return $ MC.BVValue NR.knownNat (fromIntegral i)

instance (KnownNat n, 1 <= n) => ExtractValue arch (I.I n) (BVType n) where
  extractValue (I.I i) = return $ MC.BVValue NR.knownNat (fromIntegral i)

instance (KnownNat n, 1 <= n) => ExtractValue arch (W.W n) (BVType n) where
  extractValue w = return $ MC.BVValue NR.knownNat (fromIntegral (W.unW w))

instance ExtractValue arch Int16 (BVType 16) where
  extractValue i = return $ MC.BVValue NR.knownNat (fromIntegral i)

instance ExtractValue arch D.CRBitM (BVType 4) where
  extractValue (D.CRBitM b) = return $ MC.BVValue NR.knownNat (fromIntegral b)

instance ExtractValue arch D.CRBitRC (BVType 5) where
  extractValue (D.CRBitRC b) = return $ MC.BVValue NR.knownNat (fromIntegral b)

instance ExtractValue arch D.CRRC (BVType 3) where
  extractValue (D.CRRC b) = return $ MC.BVValue NR.knownNat (fromIntegral b)

class ToPPCReg a arch tp | a arch -> tp where
  toPPCReg :: a -> R.PPCReg arch tp

instance ToPPCReg D.GPR PPC32.PPC (BVType 32) where
  toPPCReg = R.PPC_GP

instance ToPPCReg D.GPR PPC64.PPC (BVType 64) where
  toPPCReg = R.PPC_GP

instance ToPPCReg D.FR arch (BVType 128) where
  toPPCReg = R.PPC_FR
