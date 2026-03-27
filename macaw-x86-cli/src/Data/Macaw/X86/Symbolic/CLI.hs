{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.X86.Symbolic.CLI
  ( withX86Hooks
  ) where


import Data.Proxy (Proxy(..))

import Data.Parameterized.NatRepr (knownNat)

import What4.Expr (ExprBuilder)

import Lang.Crucible.Backend qualified as C
import Lang.Crucible.CLI (ExtensionSetup(..), SimulateProgramHooks, defaultSimulateProgramHooks)
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import Lang.Crucible.LLVM.DataLayout (EndianForm(LittleEndian))
import Lang.Crucible.LLVM.Intrinsics (llvmIntrinsicTypes)
import Lang.Crucible.LLVM.MemModel qualified as Mem
import Lang.Crucible.Simulator.GlobalState (insertGlobal)
import Lang.Crucible.Simulator (emptyGlobals)
import Lang.Crucible.Syntax.Concrete (ParserHooks)

import Data.Macaw.CFG qualified as DMC
import Data.Macaw.Memory qualified as DMM
import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.Symbolic.Memory qualified as DMS
import Data.Macaw.Symbolic.Syntax (machineCodeParserHooks)
import Data.Macaw.X86 (X86_64)
import Data.Macaw.X86.Symbolic (newSymFuns, x86_64MacawEvalFn)
import Data.Macaw.X86.Symbolic.Syntax (x86ParserHooks)

 -- | Small helper for providing X86_64 language-specific hooks, e.g., for use
-- with 'Lang.Crucible.CLI.execCommand'.
withX86Hooks ::
  ((?parserHooks :: ParserHooks (DMS.MacawExt X86_64)) =>
   (forall p sym bak t st fs.
     ( C.IsSymBackend sym bak
     , sym ~ ExprBuilder t st fs
     ) =>
     bak ->
     IO (ExtensionSetup p sym (DMS.MacawExt X86_64))) ->
    SimulateProgramHooks (DMS.MacawExt X86_64) ->
    IO a) ->
  IO a
withX86Hooks k = do
  ha <- newHandleAllocator
  mvar <- Mem.mkMemVar "macaw-x86:llvm_memory" ha
  let ?ptrWidth = knownNat @64
  let ?memOpts = Mem.defaultMemOptions

  let ext ::
        forall p sym bak t st fs.
        (C.IsSymBackend sym bak, sym ~ ExprBuilder t st fs) =>
        bak ->
        IO (ExtensionSetup p sym (DMS.MacawExt X86_64))
      ext bak = do
        let sym = C.backendGetSym bak
        let ?recordLLVMAnnotation = \_ _ _ -> pure ()
        let ?processMacawAssert = DMS.defaultProcessMacawAssertion
        symFns <- newSymFuns sym
        let elfMem = DMC.emptyMemory DMM.Addr64
        let eFn = x86_64MacawEvalFn symFns DMS.defaultMacawArchStmtExtensionOverride
        (initMem, ptrTable) <-
          DMS.newGlobalMemory
            (Proxy @X86_64)
            bak
            LittleEndian
            DMS.ConcreteMutable
            elfMem
        let mmConf = DMS.memModelConfig bak ptrTable
        pure ExtensionSetup
          { extImpl = DMS.macawExtensions eFn mvar mmConf
          , extIntrinsicTypes = llvmIntrinsicTypes
          , extInitGlobals = insertGlobal mvar initMem emptyGlobals
          }
  let ?parserHooks = machineCodeParserHooks (Proxy :: Proxy X86_64) x86ParserHooks
  k ext defaultSimulateProgramHooks
