{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import           Control.Monad
import           Control.Monad.ST
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as Elf
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import           System.IO
import GHC.IO (ioToST)

import qualified Data.Macaw.Architecture.Info as M
import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Memory.ElfLoader as Elf
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as MX
import qualified Data.Macaw.X86.Symbolic as MX

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.ProgramLoc as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegValue as C
import qualified Lang.Crucible.Solver.Interface as C
import qualified Lang.Crucible.Solver.SimpleBackend as C

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
      C.RV <$> C.freshConstant sym (MS.crucGenArchRegName archFns r) (C.BaseBVRepr w)
    M.TupleTypeRepr{}  ->
      error "macaw-symbolic do not support tuple types."

main :: IO ()
main = do
  putStrLn "Start test case"
  Some gen <- newIONonceGenerator
  halloc <- C.newHandleAllocator
  sym <- C.newSimpleBackend gen
  let x86ArchFns :: MS.MacawSymbolicArchFunctions MX.X86_64
      x86ArchFns = MX.x86_64MacawSymbolicFns

  let posFn :: M.MemSegmentOff 64 -> C.Position
      posFn = C.OtherPos . Text.pack . show

  let loadOpt :: Elf.LoadOptions
      loadOpt = Elf.LoadOptions { Elf.loadRegionIndex = 1
                                , Elf.loadStyle = Elf.LoadBySection
                                , Elf.includeBSS = False
                                }
  putStrLn "Read elf"
  elfContents <- BS.readFile "tests/add_ubuntu64.o"
  elf <-
    case Elf.parseElf elfContents of
      Elf.Elf64Res errs e -> do
        unless (null errs) $
          fail "Error parsing Elf file"
        pure e
      _ -> fail "Expected 64-bit elf file"
  (secIdxMap, mem) <-
    case Elf.memoryForElf loadOpt elf of
      Left err -> fail err
      Right r -> pure r

  let (symErrs, nameAddrList) = Elf.resolveElfFuncSymbols mem secIdxMap elf
  forM_ symErrs $ \err -> do
    hPutStrLn stderr $ show err

  putStrLn "Lookup addr"
  addAddr <-
    case [ addr | ("add", addr) <- nameAddrList ] of
      [addr] -> pure $! addr
      [] -> fail "Could not find add function"
      _ -> fail "Found multiple add functions"
  putStrLn $ "Addr " ++ show addAddr

  memBaseVar <- stToIO $ C.freshGlobalVar halloc "add_mem_base" C.knownRepr

  let memBaseVarMap :: MS.MemSegmentMap 64
      memBaseVarMap = Map.singleton 1 memBaseVar

  let addrSymMap :: M.AddrSymMap 64
      addrSymMap = Map.fromList [ (addr,nm) | (nm,addr) <- nameAddrList ]
  let archInfo :: M.ArchitectureInfo MX.X86_64
      archInfo =  MX.x86_64_linux_info

  let ds0 :: M.DiscoveryState MX.X86_64
      ds0 = M.emptyDiscoveryState mem addrSymMap archInfo

  putStrLn "Analyze a function"
  let logFn addr = ioToST $ do
        putStrLn $ "Analyzing " ++ show addr

  (_, Some funInfo) <- stToIO $ M.analyzeFunction logFn addAddr M.UserRequest ds0
  putStrLn "Make CFG"
  C.SomeCFG g <- stToIO $ MS.mkFunCFG x86ArchFns halloc memBaseVarMap "add" posFn funInfo

  regs <- MS.macawAssignToCrucM (mkReg x86ArchFns sym) (MS.crucGenRegAssignment x86ArchFns)
  putStrLn "Run code block"
  execResult <- MS.runCodeBlock sym x86ArchFns halloc g regs
  case execResult of
    C.FinishedExecution _ (C.TotalRes _pair) -> do
      putStrLn "Done"
    _ -> do
      fail "Partial execution returned."

{-
  -- Steps:
  -- Load up Elf file.
  -- Call symbolic simulator
  -- Check Result
-}
