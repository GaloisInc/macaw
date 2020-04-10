{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Disassemble
  ( riscvDisassembleFn
  ) where

import qualified Control.Monad.Except as E
import qualified Control.Monad.RWS as RWS
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.List as L
import qualified Data.Parameterized.Map as MapF
import qualified Data.Sequence as Seq
import qualified GHC.TypeLits as T
import qualified GRIFT.InstructionSet as G
import qualified GRIFT.Decode as G
import qualified GRIFT.Semantics as G
import qualified GRIFT.Semantics.Expand as G
import qualified GRIFT.Types as G

import           Control.Lens ((^.), (&))
import           Control.Monad.ST (ST)
import           Control.Monad.Trans (lift)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce ( NonceGenerator, freshNonce )
import           Data.Parameterized.Some (Some(..))
import           Data.Word (Word8)

import           Data.Macaw.RISCV.Arch
import           Data.Macaw.RISCV.RISCVReg

data RISCVMemoryError w = RISCVMemoryError !(MM.MemoryError w)

readBytesLE :: [Word8] -> Some BV.BitVector
readBytesLE [] = Some BV.bv0
readBytesLE (byte:rstBytes) =
  case readBytesLE rstBytes of
    Some rstBV ->
      let byteBV = BV.bitVector (fromIntegral byte) :: BV.BitVector 8
      in Some (rstBV BV.<:> byteBV)

bvWidth :: BV.BitVector w -> NatRepr w
bvWidth (BV.BitVector wRepr _) = wRepr

-- | Read a single RISC-V instruction.
readInstruction :: forall rv w . MM.MemWidth w
                => G.RVRepr rv
                -> G.InstructionSet rv
                -> MM.MemSegmentOff w
                -> Either (RISCVMemoryError w) (Some (G.Instruction rv), MM.MemWord w)
readInstruction rvRepr iset addr = do
  let seg = MM.segoffSegment addr
  case MM.segmentFlags seg `MMP.hasPerm` MMP.execute of
    False -> E.throwError (RISCVMemoryError (MM.PermissionsError (MM.segoffAddr addr)))
    True -> do
      contents <- liftMemError $ MM.segoffContentsAfter addr
      case contents of
        [] -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
        MM.RelocationRegion r : _ ->
          E.throwError (RISCVMemoryError (MM.UnexpectedRelocation (MM.segoffAddr addr) r))
        MM.BSSRegion {} : _ ->
          E.throwError (RISCVMemoryError (MM.UnexpectedBSS (MM.segoffAddr addr)))
        MM.ByteRegion bs : _rest
          | BS.null bs -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
          | otherwise -> do
              case rvRepr of
                -- If the C extension is present, first attempt to
                -- decode 2 bytes. If that fails, decode 4 bytes.
                G.RVRepr _ (G.ExtensionsRepr _ _ _ _ G.CYesRepr) -> do
                  cinstBV <- case readBytesLE (BS.unpack (BS.take 2 bs)) of
                    Some cinstBV | NatCaseEQ <- testNatCases (bvWidth cinstBV) (knownNat @16) -> return cinstBV
                    _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
                  case G.decodeC rvRepr cinstBV of
                    Just sinst -> return (sinst, 2)
                    Nothing -> do
                      instBV <- case readBytesLE (BS.unpack (BS.take 4 bs)) of
                        Some instBV | NatCaseEQ <- testNatCases (bvWidth instBV) (knownNat @32) -> return instBV
                        _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
                      return (G.decode iset instBV, 4)
                _ -> do
                  instBV <- case readBytesLE (BS.unpack (BS.take 4 bs)) of
                    Some instBV | NatCaseEQ <- testNatCases (bvWidth instBV) (knownNat @32) -> return instBV
                    _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
                  return (G.decode iset instBV, 4)

liftMemError :: Either (MM.MemoryError w) a -> Either (RISCVMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (RISCVMemoryError err)
    Right a -> Right a

------------

data DisInstEnv s ids rv fmt = DisInstEnv { disInst :: G.Instruction rv fmt
                                          , disNonceGen :: NonceGenerator (ST s) ids
                                          }

data DisInstState (rv :: G.RV) ids = DisInstState { disRegState :: MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
                                                  }

data DisInstError rv fmt = NonConstantGPR (G.InstExpr fmt rv 5)
                         | NonConstantFPR (G.InstExpr fmt rv 5)
                         | ZeroWidthExpr (G.InstExpr fmt rv 0)
                         | forall w w' . WidthNotLTExpr (G.InstExpr fmt rv w) (NatRepr w')

-- | Monad for disassembling a single instruction.
newtype DisInstM s ids rv fmt a = DisInstM
  { unDisInstM :: E.ExceptT (DisInstError rv fmt) (RWS.RWST (DisInstEnv s ids rv fmt) (Seq.Seq (MC.Stmt rv ids)) (DisInstState rv ids) (ST s)) a }
  deriving ( Functor
           , Applicative
           , Monad
           , RWS.MonadReader (DisInstEnv s ids rv fmt)
           , RWS.MonadState (DisInstState rv ids)
           , E.MonadError (DisInstError rv fmt)
           )

widthPos :: G.InstExpr fmt rv w -> (1 <= w => DisInstM s ids rv fmt a) -> DisInstM s ids rv fmt a
widthPos e a = case isZeroOrGT1 (G.exprWidth e) of
  Left Refl -> E.throwError (ZeroWidthExpr e)
  Right LeqProof -> a

widthLt :: G.InstExpr fmt rv w -> NatRepr w' -> ((w + 1) <= w' => DisInstM s ids rv fmt a) -> DisInstM s ids rv fmt a
widthLt e w a = case testNatCases (G.exprWidth e) w of
  NatCaseLT LeqProof -> a
  _ -> E.throwError (WidthNotLTExpr e w)

liftST :: ST s a -> DisInstM s ids rv fmt a
liftST = DisInstM . lift . lift

getReg :: MC.ArchReg rv tp -> DisInstM s ids rv fmt (MC.Value rv ids tp)
getReg r = do
  regState <- disRegState <$> RWS.get
  return (regState ^. MC.boundValue r)

addAssignment :: MC.AssignRhs rv (MC.Value rv ids) tp
              -> DisInstM s ids rv fmt (MC.Value rv ids tp)
addAssignment rhs = do
  ng <- disNonceGen <$> RWS.ask
  id <- liftST $ freshNonce ng
  return (MC.AssignedValue (MC.Assignment (MC.AssignId id) rhs))

disLocApp :: (1 <= w, RISCV rv)
          => G.LocApp (G.InstExpr fmt rv) rv w
          -> DisInstM s ids rv fmt (MC.Value rv ids (MT.BVType w))
disLocApp locApp = case locApp of
  G.PCApp _w -> getReg PC
  G.GPRApp _w rid -> do
    ridVal <- disInstExpr rid
    case ridVal of
      MC.BVValue _w val -> getReg (GPR (BV.bitVector val))
      _ -> E.throwError (NonConstantGPR rid)
  G.FPRApp _w rid -> do
    ridVal <- disInstExpr rid
    case ridVal of
      MC.BVValue _w val -> getReg (FPR (BV.bitVector val))
      _ -> E.throwError (NonConstantFPR rid)
  G.MemApp bytes addr -> do
    addrVal <- disInstExpr addr
    addAssignment (MC.ReadMem addrVal (MC.BVMemRepr bytes MC.LittleEndian))
  G.ResApp _addr -> error "TODO: disassemble ResApp"
  G.CSRApp _w _rid -> error "TODO: disassemble CSRApp"
  G.PrivApp -> getReg PrivLevel

disBVApp :: (1 <= w, RISCV rv)
         => G.BVApp (G.InstExpr fmt rv) w
         -> DisInstM s ids rv fmt (MC.Value rv ids (MT.BVType w))
disBVApp bvApp = case bvApp of
  G.AndApp w e1 e2 -> binaryOp (MC.BVAnd w) e1 e2
  G.OrApp w e1 e2 -> binaryOp (MC.BVOr w) e1 e2
  G.XorApp w e1 e2 -> binaryOp (MC.BVXor w) e1 e2
  G.NotApp w e -> unaryOp (MC.BVComplement w) e
  G.SllApp w e1 e2 -> binaryOp (MC.BVShl w) e1 e2
  G.SrlApp w e1 e2 -> binaryOp (MC.BVShr w) e1 e2
  G.SraApp w e1 e2 -> binaryOp (MC.BVSar w) e1 e2
  G.AddApp w e1 e2 -> binaryOp (MC.BVAdd w) e1 e2
  G.SubApp w e1 e2 -> binaryOp (MC.BVSub w) e1 e2
  G.MulApp w e1 e2 -> binaryOp (MC.BVMul w) e1 e2
  G.QuotUApp _w _e1 _e2 -> error "TODO: Disassemble QuotUApp"
  G.QuotSApp _w _e1 _e2 -> error "TODO: Disassemble QuotSApp"
  G.RemUApp _w _e1 _e2 -> error "TODO: Disassemble RemUApp"
  G.RemSApp _w _e1 _e2 -> error "TODO: Disassemble RemSApp"
  G.NegateApp _w _e -> error "TODO: Disassemble NegateApp"
  G.AbsApp _w _e -> error "TODO: Disassemble AbsApp"
  G.SignumApp _w _e -> error "TODO: Disassemble SignumApp"
  G.EqApp e1 e2 -> widthPos e1 $ binaryOpBool MC.Eq e1 e2
  G.LtuApp e1 e2 -> widthPos e1 $ binaryOpBool MC.BVSignedLt e1 e2
  G.LtsApp e1 e2 -> widthPos e1 $ binaryOpBool MC.BVUnsignedLt e1 e2
  -- TODO: The following two cases should use either extension or
  -- truncation depending on what the widths of the vectors are. They
  -- should never throw an error.
  G.ZExtApp _w _e -> error "TODO: Disassemble ZExtApp"
  G.SExtApp _w _e -> error "TODO: Disassemble SExtApp"
  G.ConcatApp _w _e1 _e2 -> error "TODO: Disassemble ConcatApp"
  G.IteApp w test e1 e2 -> do
    testVal <- disInstExpr test
    testValBool <- bvToBool testVal
    e1Val <- disInstExpr e1
    e2Val <- disInstExpr e2
    addAssignment (MC.EvalApp (MC.Mux (MT.BVTypeRepr w) testValBool e1Val e2Val))
  _ -> undefined
  where unaryOp op e = do
          eVal <- disInstExpr e
          addAssignment (MC.EvalApp (op eVal))
        binaryOp op e1 e2 = do
          e1Val <- disInstExpr e1
          e2Val <- disInstExpr e2
          addAssignment (MC.EvalApp (op e1Val e2Val))
        binaryOpBool op e1 e2 = do
          eq <- binaryOp op e1 e2
          boolToBV eq
        boolToBV bool = addAssignment (MC.EvalApp (MC.Mux (MT.BVTypeRepr (knownNat @1)) bool
                                                   (MC.BVValue knownNat 1)
                                                   (MC.BVValue knownNat 0)))
        bvToBool bv = addAssignment (MC.EvalApp (MC.Eq bv (MC.BVValue (knownNat @1) 1)))

disStateApp :: (1 <= w, RISCV rv)
            => G.StateApp (G.InstExpr fmt rv) rv w
            -> DisInstM s ids rv fmt (MC.Value rv ids (MT.BVType w))
disStateApp stateApp = case stateApp of
  G.LocApp locApp -> disLocApp locApp
  G.AppExpr bvApp -> disBVApp bvApp
  G.FloatAppExpr _flApp -> undefined

disInstExpr :: (1 <= w, RISCV rv)
            => G.InstExpr fmt rv w
            -> DisInstM s ids rv fmt (MC.Value rv ids (MT.BVType w))
disInstExpr instExpr = case instExpr of
  G.InstLitBV (BV.BitVector w val) -> return (MC.BVValue w val)
  G.InstAbbrevApp _abbrevApp -> undefined
  G.OperandExpr _w _oid -> undefined
  G.InstBytes _w -> undefined
  G.InstWord _w -> undefined
  G.InstStateApp stateApp -> disStateApp stateApp

-- | Translate a GRIFT statement into Macaw statement(s).
disStmt :: RISCV rv => G.Stmt (G.InstExpr fmt) rv -> DisInstM s ids rv fmt ()
disStmt gStmt = case gStmt of
  G.AssignStmt (G.PCApp _) gExpr -> do
    pcVal <- disInstExpr gExpr
    undefined
  G.AssignStmt _ _ -> undefined
  G.AbbrevStmt abbrevStmt -> undefined
  G.BranchStmt gExpr lStmts rStmts -> undefined

riscvDisassembleFn :: G.RVRepr rv
                   -> NonceGenerator (ST s) ids
                   -> MC.ArchSegmentOff rv
                   -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
                   -> Int
                   -> ST s (MC.Block rv ids, Int)
riscvDisassembleFn _rvRepr _nonceGen _startAddr _regState _maxSize = do
  undefined
