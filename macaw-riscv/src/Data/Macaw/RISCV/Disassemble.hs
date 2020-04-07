{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Macaw.RISCV.Disassemble
  ( riscvDisassembleFn
  ) where

import qualified Control.Monad.Except as E
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified GRIFT.InstructionSet.Known as GI
import qualified GRIFT.Decode as GD
import qualified GRIFT.Types as GT

import           Control.Monad.ST (ST)
import           Data.Parameterized.Nonce (NonceGenerator)
import           Data.Parameterized.Some (Some(..))

data RISCVMemoryError w = RISCVMemoryError !(MM.MemoryError w)

readInstruction :: forall rv w . MM.MemWidth w
                => GT.RVRepr rv
                -> MM.MemSegmentOff w
                -> Either (RISCVMemoryError w) (Some (GT.Instruction rv), MM.MemWord w)
readInstruction rvRepr addr = do
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
              cinstBV <- twoBytes bs
              (bytesRead, insn) <- case rvRepr of
                GT.RVRepr _ (GT.ExtensionsRepr _ _ _ _ GT.CYesRepr) -> case GD.decodeC rvRepr cinstBV of
                  Just sinst -> return (2, sinst)
                  Nothing -> do
                    instBV <- fourBytes bs
                    return (4, GD.decode (GI.knownISetWithRepr rvRepr) instBV)
                GT.RVRepr _ (GT.ExtensionsRepr _ _ _ _ GT.CNoRepr) -> do
                  instBV <- fourBytes bs
                  return (4, GD.decode (GI.knownISetWithRepr rvRepr) instBV)
              return (insn, fromIntegral bytesRead)
  where twoBytes :: BS.ByteString -> Either (RISCVMemoryError w) (BV.BitVector 16)
        twoBytes bs = case BS.unpack (BS.take 4 bs) of
          [b0,b1] -> return ( (BV.bitVector (fromIntegral b0) :: BV.BitVector 8) BV.<:>
                              (BV.bitVector (fromIntegral b1) :: BV.BitVector 8) )
          _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
        fourBytes :: BS.ByteString -> Either (RISCVMemoryError w) (BV.BitVector 32)
        fourBytes bs = case BS.unpack (BS.take 4 bs) of
          [b0,b1,b2,b3] -> return ( (BV.bitVector (fromIntegral b0) :: BV.BitVector 8) BV.<:>
                                    (BV.bitVector (fromIntegral b1) :: BV.BitVector 8) BV.<:>
                                    (BV.bitVector (fromIntegral b2) :: BV.BitVector 8) BV.<:>
                                    (BV.bitVector (fromIntegral b3) :: BV.BitVector 8) )
          _ -> E.throwError (RISCVMemoryError (MM.AccessViolation (MM.segoffAddr addr)))

liftMemError :: Either (MM.MemoryError w) a -> Either (RISCVMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (RISCVMemoryError err)
    Right a -> Right a

riscvDisassembleFn :: GT.RVRepr rv
                   -> forall s ids . NonceGenerator (ST s) ids
                   -> MC.ArchSegmentOff rv
                   -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
                   -> Int
                   -> ST s (MC.Block rv ids, Int)
riscvDisassembleFn _ _ _ _ = undefined
