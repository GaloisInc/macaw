{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.ARM.Simplify (
  simplifyTruncExt
  ) where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.SemMC.Simplify as MSS
import qualified Data.Macaw.Types as MT
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as PN

import qualified SemMC.Architecture.AArch32 as ARM

import           Data.Macaw.ARM.ARMReg ()
import qualified Data.Macaw.ARM.Arch as AA

import Debug.Trace
import           Text.PrettyPrint.ANSI.Leijen as PP
instance MSS.SimplifierExtension ARM.AArch32 where
  simplifyArchApp = simplifyTruncExt
  simplifyArchFn = armSimplifyArchFn

armSimplifyArchFn :: MC.ArchFn ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
                  -> MT.TypeRepr tp
                  -> Maybe (MC.Value ARM.AArch32 ids tp)
armSimplifyArchFn af _rep =
  case af of
    AA.SRem _ z@(MC.BVValue _ 0) _ -> return z
    AA.URem _ z@(MC.BVValue _ 0) _ -> return z
    AA.SDiv _ z@(MC.BVValue _ 0) _ -> return z
    AA.UDiv _ z@(MC.BVValue _ 0) _ -> return z
    _ -> Nothing

-- | Simplify terms that extend a pointer, increment it, and then truncate it
-- back to 32 bits.
--
-- These sequences interfere with the abstract interpretation of especially the
-- stack pointer, which just sends any ext/trunc operations to Top.
--
-- > r1 := (uext val 65)
-- > r2 := (bv_add r1 (constant :: [65]))
-- > r3 := (trunc r2 32)
--
-- to (bv_add val (constant :: [32]))
--
-- FIXME: Do we need to call simplifyValue on everything we find here?
simplifyTruncExt :: MC.App (MC.Value ARM.AArch32 ids) tp
                 -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyTruncExt r3 = do
  MC.Trunc r2 rep3 <- return r3
  -- -- traceM ("Simplifiying " ++ show r3)
  -- case r3 of
  --   MC.AssignedValue (MC.Assignment rid (MC.EvalApp app)) ->
  --     traceM ("Simplifying " ++ show r3 ++ " which is an assignment: " ++ show (MC.ppApp PP.pretty app))
  --   _ -> return ()
  -- MC.AssignedValue (MC.Assignment r3_id (MC.EvalApp (MC.Trunc r2 rep3))) <- return r3
  let targetSize = PN.knownNat @32
  Refl <- testEquality rep3 targetSize -- (PN.knownNat @32)
  traceM ("Trunc to 32: " ++ show r2)
  traceM ("  Argument is: " ++ show (MC.ppValueAssignments r2))
  case r2 of
    MC.AssignedValue (MC.Assignment _ (MC.EvalApp app)) -> do
      traceM ("  argument is an app: " ++ show (MC.ppApp PP.pretty app))
    other -> do
      traceM ("  argument is not an app: " ++ show other)
      return ()
  MC.AssignedValue (MC.Assignment r2_id (MC.EvalApp (MC.BVAdd rep2 r1 constant))) <- return r2
  MC.BVValue constantRepr constantVal <- return constant
  Refl <- testEquality constantRepr (PN.knownNat @65)
  traceM ("  Adding a constant: " ++ show constant)
  MC.AssignedValue (MC.Assignment r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r1
  Refl <- testEquality rep1 (PN.knownNat @65)
  traceM ("  uexting: " ++ show val)
  let MT.BVTypeRepr valwidth = MT.typeRepr val
  traceM ("  sizes: " ++ show valwidth ++ " and " ++ show targetSize ++ " " ++ show (testEquality valwidth targetSize))
  -- Refl <- testEquality (MT.typeRepr val) (MT.BVTypeRepr rep3)
  -- Refl <- testEquality valwidth rep3
  case testEquality valwidth targetSize of
    Nothing -> traceM "Size mismatch" >> Nothing
    Just Refl -> do
      traceM ("  Doing replacement (sizes work out)")
      let newConstant = MC.BVValue targetSize (PN.toSigned targetSize constantVal)
      let newApp = MC.BVAdd targetSize val newConstant
      traceM ("  Replacement is: " ++ show (MC.ppApp PP.pretty newApp))
      return newApp
