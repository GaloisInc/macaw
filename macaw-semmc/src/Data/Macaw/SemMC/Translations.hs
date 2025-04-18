{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.SemMC.Translations (
  bvconcat,
  bvselect
  ) where

import           GHC.TypeLits

import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BVType )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as NR
import qualified What4.BaseTypes as S

import           Data.Macaw.SemMC.Generator
import qualified Data.Macaw.SemMC.Simplify as MSS

-- | The implementation of bitvector concatenation
--
-- We pull this out to reduce the amount of code generated by TH
bvconcat :: ( OrdF (ArchReg arch)
            , MM.MemWidth (ArchAddrWidth arch)
            , MSS.SimplifierExtension arch
            , ShowF (ArchReg arch)
            )
         => (1 <= v, (u+1) <= w, 1 <= u, 1 <= w, (u+v) ~ w)
         => Value arch ids (BVType u)
         -> Value arch ids (BVType v)
         -> NR.NatRepr v
         -> NR.NatRepr u
         -> NR.NatRepr w
         -> Generator arch ids s (Expr arch ids (BVType w))
bvconcat bv1Val bv2Val repV repU repW = do
  S.LeqProof <- return (S.leqAdd2 (S.leqRefl repU) (S.leqProof (S.knownNat @1) repV))
  pf1@S.LeqProof <- return (S.leqAdd2 (S.leqRefl repV) (S.leqProof (S.knownNat @1) repU))
  Refl <- return (S.plusComm repU repV)
  S.LeqProof <- return (S.leqTrans pf1 (S.leqRefl repW))
  bv1Ext <- addExpr (AppExpr (UExt bv1Val repW))
  bv2Ext <- addExpr (AppExpr (UExt bv2Val repW))
  bv1Shifter <- addExpr (ValueExpr (BVValue repW (NR.intValue repV)))
  bv1Shf <- addExpr (AppExpr (BVShl repW bv1Ext bv1Shifter))
  return $ AppExpr (BVOr repW bv1Shf bv2Ext)

-- | Select @n@ bits from a @w@ bit bitvector starting at index @i@
--
-- This code is factored out of the TH module to improve compilation times.
bvselect :: ( MSS.SimplifierExtension arch
            , OrdF (ArchReg arch)
            , MM.MemWidth (ArchAddrWidth arch)
            , ShowF (ArchReg arch)
            )
         => (1 <= w, 1 <= n, i + n <= w)
         => Value arch ids (BVType w)
         -> NR.NatRepr n
         -> NR.NatRepr i
         -> NR.NatRepr w
         -> Generator arch ids s (Expr arch ids (BVType n))
bvselect bvVal repN repI repW = do
  Just S.LeqProof <- return (S.testLeq (repN `S.addNat` (NR.knownNat @1)) repW)
  pf1@S.LeqProof <- return $ S.leqAdd2 (S.leqRefl repI) (S.leqProof (NR.knownNat @1) repN)
  pf2@S.LeqProof <- return $ S.leqAdd (S.leqRefl (NR.knownNat @1)) repI
  Refl <- return (S.plusComm (NR.knownNat @1) repI)
  pf3@S.LeqProof <- return $ S.leqTrans pf2 pf1
  S.LeqProof <- return $ S.leqTrans pf3 (S.leqProof (repI `S.addNat` repN) repW)
  bvShf <- addExpr (AppExpr (BVShr repW bvVal (mkLit repW (NR.intValue repI))))
  return (AppExpr (Trunc bvShf repN))
