{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Proxy (Proxy(..))

import Data.Parameterized.NatRepr (knownNat)

import Lang.Crucible.Backend qualified as C
import Lang.Crucible.CLI (defaultSimulateProgramHooks)
import Lang.Crucible.CLI.Options qualified as Opts
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import Lang.Crucible.LLVM.MemModel qualified as Mem

import Data.Macaw.CFG qualified as DMC
import Data.Macaw.Memory qualified as DMM
import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.Symbolic.Memory qualified as DMS
import Data.Macaw.Symbolic.Syntax (machineCodeParserHooks)
import Data.Macaw.X86 (X86_64)
import Data.Macaw.X86.Symbolic (newSymFuns, x86_64MacawEvalFn)
import Data.Macaw.X86.Symbolic.CLI ()
import Data.Macaw.X86.Symbolic.Syntax (x86ParserHooks)

main :: IO ()
main = do
  let ?parserHooks = machineCodeParserHooks (Proxy :: Proxy X86_64) x86ParserHooks
  ha <- newHandleAllocator
  mvar <- Mem.mkMemVar "llvm_memory" ha
  let ?ptrWidth = knownNat @64
  let ?memOpts = Mem.defaultMemOptions
  Opts.main
    "macaw-x86"
    (\bak -> do
      let sym = C.backendGetSym bak
      let ?recordLLVMAnnotation = \_ _ _ -> pure ()
      symFns <- newSymFuns sym
      let elfMem = DMC.emptyMemory DMM.Addr64
      let eFn = x86_64MacawEvalFn symFns DMS.defaultMacawArchStmtExtensionOverride
      (_initMem, ptrTable) <-
        DMS.newGlobalMemory
          (Proxy @X86_64)
          bak
          LittleEndian
          DMS.ConcreteMutable
          elfMem
      -- TOOD?
      -- C.writeGlobal mvar initMem
      let mmConf = DMS.memModelConfig bak ptrTable
      pure (DMS.macawExtensions eFn mvar mmConf))
    defaultSimulateProgramHooks
