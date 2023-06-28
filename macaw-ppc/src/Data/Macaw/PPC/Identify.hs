{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.PPC.Identify
  ( identifyCall
  , identifyReturn
  , matchReturn
  )
where

import           Control.Lens ( (^.) )
import           Control.Monad ( when )
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Sequence as Seq

import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery.AbsEval as DE
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import qualified SemMC.Architecture.PPC as SP

import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg
import           Control.Applicative ((<|>))

-- | Our current heuristic is that we are issuing a (potentially conditional)
-- call if we see an address in the link register.
--
-- This seems reasonable, as the only time the link register would be populated
-- with a constant is at a call site.  This might be a problem if we see a
-- @mtlr@ and put a stack value into the link register.  That might look like a
-- call...
identifyCall :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
             => proxy var
             -> MM.Memory (MC.ArchAddrWidth ppc)
             -> Seq.Seq (MC.Stmt ppc ids)
             -> MC.RegState (PPCReg var) (MC.Value ppc ids)
             -> Maybe (Seq.Seq (MC.Stmt ppc ids), MC.ArchSegmentOff ppc)
identifyCall _ mem stmts0 rs
  | not (null stmts0)
  , MC.RelocatableValue {} <- rs ^. MC.boundValue PPC_LNK
  , Just retVal <- simplifyValue (rs ^. MC.boundValue PPC_LNK)
  , Just retAddrVal <- MC.valueAsMemAddr retVal
  , Just retAddr <- MM.asSegmentOff mem retAddrVal =
      Just (stmts0, retAddr)
  | otherwise = Nothing


-- | Called to determine if the instruction sequence contains a return
-- from the current function.
--
-- An instruction executing a return from a function will place the
-- Macaw 'ReturnAddr' value (placed in the LNK register by
-- 'mkInitialAbsState') into the instruction pointer.
identifyReturn :: (PPCArchConstraints var)
               => proxy var
               -> Seq.Seq (MC.Stmt (SP.AnyPPC var) ids)
               -> MC.RegState (PPCReg var) (MC.Value (SP.AnyPPC var) ids)
               -> MA.AbsProcessorState (PPCReg var) ids
               -> MI.Classifier (Seq.Seq (MC.Stmt (SP.AnyPPC var) ids))
identifyReturn _ stmts regState absState = do
  Some MA.ReturnAddr <- matchReturn absState (regState ^. MC.boundValue MC.ip_reg)
  return stmts

matchReturn :: forall ppc var ids w
             . (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
            => MA.AbsProcessorState (PPCReg var) ids
            -> MC.Value ppc ids (MT.BVType (SP.AddrWidth var))
            -> MI.Classifier (Some (MA.AbsValue w))
matchReturn absProcState' ip = matchRead True "bare matchRead" ip <|> matchShift ip
  where
    {- example:
      r15 := (bv_shr r13 (0x2 :: [32]))
      r16 := (trunc r15 30)
      r17 := (uext r16 32)
      r18 := (bv_shl r17 (0x2 :: [32]))
    -}
    matchShift r = do
      MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.BVShl _ addr (MC.BVValue _ shiftAmt)))) <- return r
      MI.classifierGuard "shiftAmt == 0x2" (shiftAmt == 0x2)
      Some (MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.BVShr _ addr' (MC.BVValue _ shiftAmt'))))) <- return (stripExtTrunc addr)
      MI.classifierGuard "shiftAmt' == 0x2" (shiftAmt' == 0x2)
      case MA.transferValue absProcState' addr' of
        MA.ReturnAddr -> return (Some MA.ReturnAddr)
        _ -> matchRead False "matchShift call" addr'

    {- example:
      r8 := (bv_add r1_0 (0x14 :: [32]))
      r9 := read_mem r8 (bvbe4)
    -}
    matchRead :: forall w2. Bool -> String -> MC.Value ppc ids (MT.BVType w2) -> MI.Classifier (Some (MA.AbsValue w))
    matchRead strict token r = do
      MI.classifierLog $ "matchRead(" <> token <> "): r is " <> (show $ MC.ppValueAssignments r)
      MC.AssignedValue (MC.Assignment _ (MC.ReadMem readAddr memRep)) <- return r
      MI.classifierLog $ "matchRead(" <> token <> "): " <> (show $ DE.absEvalReadMem absProcState' readAddr memRep)

      () <- case DE.absEvalReadMem absProcState' readAddr memRep of
          MA.ReturnAddr -> return ()
          MA.TopV       -> when strict $ fail $ "matchRead(" <> token <> "): strict but no return addr"
          _             -> fail $ "matchRead(" <> token <> "): unexpected abstract value"

      return $ Some MA.ReturnAddr

-- | Look at a value; if it is a trunc, sext, or uext, strip that off and return
-- the underlying value.  If it isn't, just return the value
stripExtTrunc :: MC.Value (SP.AnyPPC v) ids tp -> Some (MC.Value (SP.AnyPPC v) ids)
stripExtTrunc v =
  case v of
    MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.Trunc v' _))) -> stripExtTrunc v'
    MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.SExt v' _))) -> stripExtTrunc v'
    MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.UExt v' _))) -> stripExtTrunc v'
    _ -> Some v
