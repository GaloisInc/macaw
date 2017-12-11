{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Instance definitions to assist in extracting Macaw values from instruction operands
--
-- This module is full of orphans, as the definitions of the classes are in a
-- package that cannot depend on the architecture-specific backends.
module Data.Macaw.PPC.Operand () where

import           GHC.TypeLits
import           Data.Int ( Int16 )
import           Data.Word ( Word32 )
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Macaw.CFG.Core as MC
import           Data.Macaw.Types
import qualified Data.Word.Indexed as W
import qualified Data.Int.Indexed as I
import qualified Dismantle.PPC as D

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import qualified Data.Macaw.SemMC.Generator as G
import           Data.Macaw.SemMC.Operands
import qualified Data.Macaw.PPC.PPCReg as R

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

instance (MC.ArchReg ppc ~ R.PPCReg ppc) => ExtractValue ppc D.FR (BVType 128) where
  extractValue (D.FR fr) = G.getRegValue (R.PPC_FR (D.VSReg fr))

instance (MC.ArchReg ppc ~ R.PPCReg ppc) => ExtractValue ppc D.VR (BVType 128) where
  extractValue (D.VR vr) = G.getRegValue (R.PPC_FR (D.VSReg (vr + 32)))

instance (MC.ArchReg ppc ~ R.PPCReg ppc) => ExtractValue ppc D.VSReg (BVType 128) where
  extractValue (D.VSReg vsr) = G.getRegValue (R.PPC_FR (D.VSReg vsr))

instance ExtractValue arch D.AbsBranchTarget (BVType 24) where
  extractValue (D.ABT w) = return $ MC.BVValue NR.knownNat (toIntegerWord w)

instance ExtractValue arch D.CondBranchTarget (BVType 14) where
  extractValue (D.CBT i) = return $ MC.BVValue NR.knownNat (toIntegerWord i)

instance ExtractValue arch D.AbsCondBranchTarget (BVType 14) where
  extractValue (D.ACBT w) = return $ MC.BVValue NR.knownNat (toIntegerWord w)

instance ExtractValue arch D.BranchTarget (BVType 24) where
  extractValue (D.BT i) = return $ MC.BVValue NR.knownNat (toIntegerWord i)

instance (KnownNat n, 1 <= n) => ExtractValue arch (I.I n) (BVType n) where
  extractValue (I.I i) = return $ MC.BVValue NR.knownNat (toIntegerWord i)

instance (KnownNat n, 1 <= n) => ExtractValue arch (W.W n) (BVType n) where
  extractValue w = return $ MC.BVValue NR.knownNat (toIntegerWord (W.unW w))

instance ExtractValue arch Int16 (BVType 16) where
  extractValue i = return $ MC.BVValue NR.knownNat (toIntegerWord i)

instance ExtractValue arch D.CRBitM (BVType 4) where
  extractValue (D.CRBitM b) = return $ MC.BVValue NR.knownNat (toIntegerWord b)

instance ExtractValue arch D.CRBitRC (BVType 5) where
  extractValue (D.CRBitRC b) = return $ MC.BVValue NR.knownNat (toIntegerWord b)

instance ExtractValue arch D.CRRC (BVType 3) where
  extractValue (D.CRRC b) = return $ MC.BVValue NR.knownNat (toIntegerWord b)

instance ToRegister D.GPR (R.PPCReg PPC32.PPC) (BVType 32) where
  toRegister = R.PPC_GP

instance ToRegister D.GPR (R.PPCReg PPC64.PPC) (BVType 64) where
  toRegister = R.PPC_GP

instance ToRegister D.FR (R.PPCReg arch) (BVType 128) where
  toRegister (D.FR rnum) = R.PPC_FR (D.VSReg rnum)

instance ToRegister D.VR (R.PPCReg arch) (BVType 128) where
  toRegister (D.VR vrnum) = R.PPC_FR (D.VSReg (vrnum + 32))

instance ToRegister D.VSReg (R.PPCReg arch) (BVType 128) where
  toRegister = R.PPC_FR

-- | Convert to a positive integer through a word type
--
-- We convert through a word because the integer returned is not allowed to be
-- negative.  Negative values must be converted to an unsigned word form, which
-- we can then promote to Integer.
--
-- For PowerPC, Word32 is large enough to accommodate all literal values
toIntegerWord :: (Integral a) => a -> Integer
toIntegerWord i = toInteger w
  where
    w :: Word32
    w = fromIntegral i
