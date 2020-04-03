{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import           Control.Monad
import           Control.Monad.ST
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as Elf
import           Data.IORef
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as Text
import           GHC.IO (ioToST)
import           System.IO

import qualified Data.Macaw.Architecture.Info as M
import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Memory.ElfLoader as Elf
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MSM
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as MX
import qualified Data.Macaw.X86.Symbolic as MX

import qualified What4.ProgramLoc as C
import qualified What4.Interface as C

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Backend.Simple as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C
import           Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import qualified Lang.Crucible.LLVM.MemModel as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegValue as C

mkReg :: (C.IsSymInterface sym, M.HasRepr (M.ArchReg arch) M.TypeRepr)
      => MS.MacawSymbolicArchFunctions arch
      -> sym
      -> M.ArchReg arch tp
      -> IO (C.RegValue' sym (MS.ToCrucibleType tp))
mkReg archFns sym r =
  case M.typeRepr r of
    M.BoolTypeRepr ->
      C.RV <$> C.freshConstant sym (MS.crucGenArchRegName archFns r) C.BaseBoolRepr
    M.BVTypeRepr w ->
      C.RV <$> (C.llvmPointer_bv sym =<< C.freshConstant sym (MS.crucGenArchRegName archFns r) (C.BaseBVRepr w))
    M.TupleTypeRepr{}  ->
      error "macaw-symbolic do not support tuple types."
    M.FloatTypeRepr{}  ->
      error "macaw-symbolic do not support float types."
    M.VecTypeRepr{}  ->
      error "macaw-symbolic do not support vector types."

main :: IO ()
main = do
  Some (gen :: NonceGenerator IO t) <- newIONonceGenerator
  halloc <- C.newHandleAllocator
  sym <- C.newSimpleBackend C.FloatRealRepr gen

  let x86ArchFns :: MS.MacawSymbolicArchFunctions MX.X86_64
      x86ArchFns = MX.x86_64MacawSymbolicFns

  let posFn :: M.MemSegmentOff 64 -> C.Position
      posFn = C.OtherPos . Text.pack . show

  elfContents <- BS.readFile "tests/add_ubuntu64"
  elf <-
    case Elf.parseElf elfContents of
      Elf.Elf64Res errs e -> do
        unless (null errs) $
          fail "Error parsing Elf file"
        pure e
      _ -> fail "Expected 64-bit elf file"

  let loadOpt :: Elf.LoadOptions
      loadOpt = Elf.defaultLoadOptions
  (mem, nameAddrList) <-
    case Elf.resolveElfContents loadOpt elf of
      Left err -> fail err
      Right (warn, mem, _mentry, nameAddrList)  -> do
        forM_ warn $ \err -> do
          hPutStrLn stderr err
        pure (mem, nameAddrList)

  addAddr <-
    case [ Elf.memSymbolStart msym | msym <- nameAddrList, Elf.memSymbolName msym == "add" ] of
      [addr] -> pure $! addr
      [] -> fail "Could not find add function"
      _ -> fail "Found multiple add functions"

  let addrSymMap :: M.AddrSymMap 64
      addrSymMap = Map.fromList [ (Elf.memSymbolStart msym, Elf.memSymbolName msym)
                                | msym <- nameAddrList ]
  let archInfo :: M.ArchitectureInfo MX.X86_64
      archInfo =  MX.x86_64_linux_info

  let ds0 :: M.DiscoveryState MX.X86_64
      ds0 = M.emptyDiscoveryState mem addrSymMap archInfo

  let logFn addr = ioToST $ do
        putStrLn $ "Analyzing " ++ show addr

  (_, Some funInfo) <- stToIO $ M.analyzeFunction logFn addAddr M.UserRequest ds0
  C.SomeCFG g <- MS.mkFunCFG x86ArchFns halloc "add" posFn funInfo

  regs <- MS.macawAssignToCrucM (mkReg x86ArchFns sym) (MS.crucGenRegAssignment x86ArchFns)

  symFuns <- MX.newSymFuns sym

  (initMem, memPtrTbl) <-  MSM.newGlobalMemory (Proxy @MX.X86_64) sym LittleEndian MSM.ConcreteMutable mem
  let globalMap = MSM.mapRegionPointers memPtrTbl

  bbMapRef <- newIORef mempty
  let ?badBehaviorMap = bbMapRef

  let lookupFn :: MS.LookupFunctionHandle sym MX.X86_64
      lookupFn = MS.LookupFunctionHandle $ \_s _mem _regs -> do
        fail "Could not find function handle."
  let validityCheck :: MS.MkGlobalPointerValidityAssertion sym 64
      validityCheck _ _ _ _ = return Nothing
  execResult <-
     MS.runCodeBlock sym x86ArchFns (MX.x86_64MacawEvalFn symFuns)
        halloc (initMem, globalMap) lookupFn validityCheck g regs
  case execResult of
    (_,C.FinishedResult _ (C.TotalRes _pair))-> do
      pure ()
    _ -> do
      pure () -- For now, we are ok with this.

{-
  -- Steps:
  -- Load up Elf file.
  -- Call symbolic simulator
  -- Check Result
-}
