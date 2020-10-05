{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Disassemble
  ( riscvDisassembleFn
  ) where

import qualified Control.Monad.Except as E
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.List as L
import qualified GRIFT.InstructionSet as G
import qualified GRIFT.InstructionSet.Known as G
import qualified GRIFT.Decode as G
import qualified GRIFT.Semantics as G
import qualified GRIFT.Semantics.Expand as G
import qualified GRIFT.Types as G
import qualified Data.Sequence as Seq
import qualified Data.Text as T

import           Control.Lens ((^.))
import           Control.Monad.ST (ST)
import           Data.Parameterized (showF)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce (NonceGenerator)
import           Data.Parameterized.Some (Some(..))
import           Data.Word (Word8)

import           Data.Macaw.RISCV.Arch
import           Data.Macaw.RISCV.RISCVReg
import           Data.Macaw.RISCV.Disassemble.Monad

data RISCVMemoryError w = RISCVMemoryError !(MM.MemoryError w)
                        | IllegalInstruction
  deriving Show

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
                -> Either (RISCVMemoryError w) (Integer, Some (G.Instruction rv), Integer)
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
              (instBV, Some inst, instBytes) <- case rvRepr of
                -- If the C extension is present, first attempt to
                -- decode 2 bytes. If that fails, decode 4 bytes.
                G.RVRepr _ (G.ExtensionsRepr _ _ _ _ G.CYesRepr) -> do
                  cinstBV <- case readBytesLE (BS.unpack (BS.take 2 bs)) of
                    Some cinstBV | NatCaseEQ <- testNatCases (bvWidth cinstBV) (knownNat @16) -> return cinstBV
                    _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
                  case G.decodeC rvRepr cinstBV of
                    Just sinst -> return (BV.bvIntegerU cinstBV, sinst, 2)
                    Nothing -> do
                      instBV <- case readBytesLE (BS.unpack (BS.take 4 bs)) of
                        Some instBV | NatCaseEQ <- testNatCases (bvWidth instBV) (knownNat @32) -> return instBV
                        _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
                      return (BV.bvIntegerU instBV, G.decode iset instBV, 4)
                _ -> do
                  instBV <- case readBytesLE (BS.unpack (BS.take 4 bs)) of
                    Some instBV | NatCaseEQ <- testNatCases (bvWidth instBV) (knownNat @32) -> return instBV
                    _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
                  return (BV.bvIntegerU instBV, G.decode iset instBV, 4)
              case inst of
                (G.Inst G.Illegal _) -> E.throwError IllegalInstruction
                _ -> return (instBV, Some inst, instBytes)

liftMemError :: Either (MM.MemoryError w) a -> Either (RISCVMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (RISCVMemoryError err)
    Right a -> Right a

widthPos :: G.InstExpr fmt rv w -> (1 <= w => DisInstM s ids rv fmt a) -> DisInstM s ids rv fmt a
widthPos e a = case isZeroOrGT1 (G.exprWidth e) of
  Left Refl -> E.throwError (ZeroWidthExpr e)
  Right LeqProof -> a

disLocApp :: (1 <= w, G.KnownRV rv)
          => G.LocApp (G.InstExpr fmt rv) rv w
          -> DisInstM s ids rv fmt (MC.Value (RISCV rv) ids (MT.BVType w))
disLocApp locApp = case locApp of
  G.PCApp _w -> getReg PC
  G.GPRApp _w ridExpr -> do
    rid <- disInstExpr ridExpr
    case rid of
      MC.BVValue _w 0 -> return (MC.BVValue knownNat 0)
      MC.BVValue _w ridVal -> getReg (GPR (BV.bitVector ridVal))
      _ -> E.throwError (NonConstantGPR ridExpr)
  G.FPRApp _w ridExpr -> do
    rid <- disInstExpr ridExpr
    case rid of
      MC.BVValue _w ridVal -> getReg (FPR (BV.bitVector ridVal))
      _ -> E.throwError (NonConstantFPR ridExpr)
  G.MemApp bytes addrExpr -> do
    addr <- disInstExpr addrExpr
    readMem addr (MC.BVMemRepr bytes MC.LittleEndian)
  G.ResApp _addr -> error "TODO: disassemble ResApp"
  G.CSRApp _w _rid -> do
    setReg EXC (MC.BoolValue True)
    return (MC.BVValue knownNat 0)
  G.PrivApp -> getReg PrivLevel

disBVApp :: (1 <= w, G.KnownRV rv)
         => G.BVApp (G.InstExpr fmt rv) w
         -> DisInstM s ids rv fmt (MC.Value (RISCV rv) ids (MT.BVType w))
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
  G.LtsApp e1 e2 -> widthPos e1 $ binaryOpBool MC.BVSignedLt e1 e2
  G.LtuApp e1 e2 -> widthPos e1 $ binaryOpBool MC.BVUnsignedLt e1 e2
  -- In GRIFT, we use "ext" to truncate bitvectors, which is weird but
  -- true. So we have to check the widths fo the expressions involved
  -- and emit either an extension, a truncation, or just return the
  -- expression back.
  G.ZExtApp w e -> widthPos e $ do
    eVal <- disInstExpr e
    case testNatCases w (G.exprWidth e) of
      NatCaseGT LeqProof -> evalApp (MC.UExt eVal w)
      NatCaseEQ -> return eVal
      NatCaseLT LeqProof -> evalApp (MC.Trunc eVal w)
  G.SExtApp w e -> widthPos e $ do
    eVal <- disInstExpr e
    case testNatCases w (G.exprWidth e) of
      NatCaseGT LeqProof -> evalApp (MC.SExt eVal w)
      NatCaseEQ -> return eVal
      NatCaseLT LeqProof -> evalApp (MC.Trunc eVal w)
  -- We sometimes "extract" the entire expression, so this should just
  -- get translated to the expression itself.
  G.ExtractApp w ix e -> widthPos e $ do
    eVal <- disInstExpr e
    let eWidth = G.exprWidth e
        shiftAmount = MC.BVValue eWidth (intValue ix)
    shiftedVal <- evalApp (MC.BVShr eWidth eVal shiftAmount)
    case testNatCases w (G.exprWidth e) of
      NatCaseLT LeqProof -> evalApp (MC.Trunc shiftedVal w)
      NatCaseEQ -> return shiftedVal
      _ -> E.throwError $ BadExprWidth e
  G.ConcatApp w e1 e2 -> case (isZeroOrGT1 (G.exprWidth e1),
                               isZeroOrGT1 (G.exprWidth e2)) of
    (Right e1PosProof@LeqProof, Right e2PosProof@LeqProof) -> do
      e1Val <- disInstExpr e1
      e2Val <- disInstExpr e2
      LeqProof <- return $ leqAdd2 (leqRefl e1) e2PosProof
      LeqProof <- return $ leqAdd2 e1PosProof (leqRefl e2)
      Refl <- return $ plusComm (knownNat @1) e2
      e1ExtVal <- evalApp (MC.UExt e1Val w)
      e2ExtVal <- evalApp (MC.UExt e2Val w)
      let shiftAmount = MC.BVValue w (intValue w - intValue (G.exprWidth e1))
      e1ShiftedVal <- evalApp (MC.BVShl w e1ExtVal shiftAmount)
      evalApp (MC.BVOr w e1ShiftedVal e2ExtVal)
    _ -> error "FOO"
  G.IteApp w test e1 e2 -> do
    testVal <- disInstExpr test
    testValBool <- bvToBool testVal
    e1Val <- disInstExpr e1
    e2Val <- disInstExpr e2
    evalApp (MC.Mux (MT.BVTypeRepr w) testValBool e1Val e2Val)
  where unaryOp op e = do
          eVal <- disInstExpr e
          evalApp (op eVal)
        binaryOp op e1 e2 = do
          e1Val <- disInstExpr e1
          e2Val <- disInstExpr e2
          evalApp (op e1Val e2Val)
        binaryOpBool op e1 e2 = do
          eq <- binaryOp op e1 e2
          boolToBV eq
        boolToBV bool = evalApp (MC.Mux (MT.BVTypeRepr (knownNat @1)) bool
                                  (MC.BVValue knownNat 1)
                                  (MC.BVValue knownNat 0))
        bvToBool bv = evalApp (MC.Eq bv (MC.BVValue (knownNat @1) 1))

disStateApp :: (1 <= w, G.KnownRV rv)
            => G.StateApp (G.InstExpr fmt rv) rv w
            -> DisInstM s ids rv fmt (MC.Value (RISCV rv) ids (MT.BVType w))
disStateApp stateApp = case stateApp of
  G.LocApp locApp -> disLocApp locApp
  G.AppExpr bvApp -> disBVApp bvApp
  G.FloatAppExpr _flApp -> error "TODO: Disassemble FloatAppExpr"

instOperand :: G.OperandID fmt w -> G.Instruction rv fmt -> BV.BitVector w
instOperand (G.OperandID oix) (G.Inst _ (G.Operands _ operands)) = operands L.!! oix

disInstExpr :: (1 <= w, G.KnownRV rv)
            => G.InstExpr fmt rv w
            -> DisInstM s ids rv fmt (MC.Value (RISCV rv) ids (MT.BVType w))
disInstExpr instExpr = case instExpr of
  G.InstLitBV (BV.BitVector w val) -> return (MC.BVValue w val)
  G.InstAbbrevApp abbrevApp -> disInstExpr (G.expandAbbrevApp abbrevApp)
  G.OperandExpr w oid -> do
    inst <- getDisInst
    let BV.BitVector _ val = instOperand oid inst
    return (MC.BVValue w val)
  G.InstBytes w -> do
    instBytes <- getDisInstBytes
    return (MC.BVValue w instBytes)
  G.InstWord w -> do
    instWord <- getDisInstWord
    return (MC.BVValue w instWord)
  G.InstStateApp stateApp -> disStateApp stateApp

data AssignStmt expr rv = forall w . AssignStmt !(G.LocApp (expr rv) rv w) !(expr rv w)

-- | Convert a 'G.Stmt' into a list of assignment statements.
collapseStmt :: G.KnownRV rv => G.Stmt (G.InstExpr fmt) rv -> [AssignStmt (G.InstExpr fmt) rv]
collapseStmt stmt = case stmt of
  G.AssignStmt loc e -> [AssignStmt loc e]
  G.AbbrevStmt abbrevStmt -> mconcat (F.toList (collapseStmt <$> (G.expandAbbrevStmt abbrevStmt)))
  G.BranchStmt testExpr lStmts rStmts ->
    let lAssignStmts = mconcat (F.toList (collapseStmt <$> F.toList lStmts))
        rAssignStmts = mconcat (F.toList (collapseStmt <$> F.toList rStmts))
    in collectBranch testExpr lAssignStmts rAssignStmts
  where collectBranch testExpr lAssignStmts rAssignStmts =
          [ AssignStmt loc (G.iteE testExpr e (G.stateExpr (G.LocApp loc))) | AssignStmt loc e <- lAssignStmts ] ++
          [ AssignStmt loc (G.iteE testExpr (G.stateExpr (G.LocApp loc)) e) | AssignStmt loc e <- rAssignStmts ]

disAssignStmt :: (RISCVConstraints rv, G.KnownRV rv) => AssignStmt (G.InstExpr fmt) rv -> DisInstM s ids rv fmt ()
disAssignStmt stmt = case stmt of
  AssignStmt (G.PCApp _) valExpr -> do
    val <- disInstExpr valExpr
    setReg PC val
  AssignStmt (G.GPRApp _ ridExpr) valExpr -> do
    rid <- disInstExpr ridExpr
    val <- disInstExpr valExpr
    case rid of
      MC.BVValue _ 0 -> return () -- it's ok to assign to x0; the value
                                  -- just gets thrown out
      MC.BVValue _ ridVal -> setReg (GPR (BV.bitVector ridVal)) val
      _ -> E.throwError (NonConstantGPR ridExpr)
  AssignStmt (G.FPRApp _ ridExpr) valExpr -> do
    rid <- disInstExpr ridExpr
    val <- disInstExpr valExpr
    case rid of
      MC.BVValue _ ridVal -> setReg (FPR (BV.bitVector ridVal)) val
      _ -> E.throwError (NonConstantGPR ridExpr)
  AssignStmt (G.MemApp bytes addrExpr) valExpr -> withLeqProof (leqMulPos (knownNat @8) bytes) $ do
    addr <- disInstExpr addrExpr
    val <- disInstExpr valExpr
    writeMem addr (MC.BVMemRepr bytes MC.LittleEndian) val
  AssignStmt (G.ResApp _addr) _valExpr -> error "TODO: Disassemble ResApp"
  AssignStmt (G.CSRApp _w _rid) _valExpr -> setReg EXC (MC.BoolValue True)
  AssignStmt G.PrivApp valExpr -> do
    val <- disInstExpr valExpr
    setReg PrivLevel val

-- | Translate a GRIFT assignment statement into Macaw statement(s).
disStmt :: (RISCVConstraints rv, G.KnownRV rv) => G.Stmt (G.InstExpr fmt) rv -> DisInstM s ids rv fmt ()
disStmt stmt = F.traverse_ disAssignStmt (collapseStmt stmt)

disassembleBlock :: RISCVConstraints rv
                 => G.RVRepr rv
                 -- ^ The RISC-V configuration
                 -> G.InstructionSet rv
                 -- ^ The RISC-V instruction set for this particular
                 -- RISC-V configuration
                 -> Seq.Seq (MC.Stmt (RISCV rv) ids)
                 -- ^ The statements disassembled thus far
                 -> MC.RegState (MC.ArchReg (RISCV rv)) (MC.Value (RISCV rv) ids)
                 -- ^ The register state at this point of the block
                 -> NonceGenerator (ST s) ids
                 -- ^ The nonce generator used for block disassembly
                 -> MC.ArchSegmentOff (RISCV rv)
                 -- ^ The current program counter value
                 -> MM.MemWord (MC.ArchAddrWidth (RISCV rv))
                 -- ^ The current offset into the block
                 -> MM.MemWord (MC.ArchAddrWidth (RISCV rv))
                 -- ^ The maximum offset we should disassemble to
                 -> ST s (MC.Block (RISCV rv) ids, MM.MemWord (MC.ArchAddrWidth (RISCV rv)))
                 -- ^ Return the disassembled block and its size.
disassembleBlock rvRepr iset blockStmts blockState ng curIPAddr blockOff maxOffset = G.withRV rvRepr $ do
  case readInstruction rvRepr iset curIPAddr of
    Left err -> do
      let block = MC.Block { MC.blockStmts = F.toList blockStmts
                           , MC.blockTerm = MC.TranslateError blockState (T.pack (show err))
                           }
      return (block, blockOff)
    Right (instWord, Some i@(G.Inst opcode _), bytesRead) -> do
      -- traceM $ "  II[" <> show curIPAddr <> "]: " <> show opcode
      let G.InstSemantics sem _ = G.semanticsFromOpcode iset opcode
      (status, disInstState, instStmts') <- runDisInstM i bytesRead instWord ng blockState $ F.traverse_ disStmt (sem ^. G.semStmts)
      let regUpdates = disInstRegUpdates disInstState
          blockState' = disInstState ^. disInstRegState
      -- TODO: Add instruction name and semantics description?
      let instStmts = (MC.InstructionStart blockOff (T.pack $ showF i) Seq.<|
                       MC.Comment "" Seq.<|
                       instStmts') Seq.|>
                      MC.ArchState (MM.segoffAddr curIPAddr) regUpdates
      let blockStmts' = blockStmts <> instStmts
      let blockOff' = blockOff + fromIntegral bytesRead
      case status of
        Left err -> do
          let block = MC.Block { MC.blockStmts = F.toList blockStmts
                               , MC.blockTerm = MC.TranslateError blockState (T.pack (show err))
                               }
          return (block, blockOff)
        Right _ -> case (isBlockTerminator opcode,
                         blockOff' >= maxOffset,
                         MM.incSegmentOff curIPAddr (fromIntegral bytesRead)) of
          (False, False, Just nextIPAddr) ->
            disassembleBlock rvRepr iset blockStmts' blockState' ng nextIPAddr blockOff' maxOffset
          _ -> do
            let block = MC.Block { MC.blockStmts = F.toList blockStmts'
                                 , MC.blockTerm = MC.FetchAndExecute blockState'
                                 }
            return (block, blockOff + fromIntegral bytesRead)
  where isBlockTerminator :: G.Opcode rv fmt -> Bool
        isBlockTerminator G.Jal = True
        isBlockTerminator G.Jalr = True
        isBlockTerminator G.Ecall = True
        isBlockTerminator G.Ebreak = True
        isBlockTerminator G.Beq = True
        isBlockTerminator G.Bne = True
        isBlockTerminator G.Blt = True
        isBlockTerminator G.Bge = True
        isBlockTerminator G.Bltu = True
        isBlockTerminator G.Bgeu = True
        isBlockTerminator G.Mret = True
        isBlockTerminator _ = False

riscvDisassembleFn :: RISCVConstraints rv
                   => G.RVRepr rv
                   -> NonceGenerator (ST s) ids
                   -> MC.ArchSegmentOff (RISCV rv)
                   -> MC.RegState (MC.ArchReg (RISCV rv)) (MC.Value (RISCV rv) ids)
                   -> Int
                   -> ST s (MC.Block (RISCV rv) ids, Int)
riscvDisassembleFn rvRepr ng startAddr regState maxSize = do
  (block, bytes) <- disassembleBlock rvRepr (G.knownISetWithRepr rvRepr) mempty regState ng startAddr 0 (fromIntegral maxSize)
  return (block, fromIntegral bytes)
