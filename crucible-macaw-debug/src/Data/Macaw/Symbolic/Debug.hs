{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Symbolic.Debug
  ( MacawCommand
  , macawCommandExt
  , macawExtImpl
  ) where

import Control.Lens qualified as Lens
import Data.BitVector.Sized qualified as BV
import Data.ByteString (ByteString)
import Data.ElfEdit qualified as Elf
import Data.Functor.Const (Const(Const, getConst))
import Data.Functor.Product (Product(Pair))
import Data.List qualified as List
import Data.Macaw.CFG qualified as M
import Data.Macaw.Dwarf qualified as D
import Data.Macaw.Symbolic qualified as M
import Data.Macaw.Symbolic.DwarfInfo (SourceLocation(..))
import Data.Macaw.Symbolic.DwarfInfo qualified as DI
import Data.Macaw.Symbolic.Regs qualified as M
import Data.Maybe qualified as Maybe
import Data.Parameterized.Classes (knownRepr, ixF', OrdF)
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.SymbolRepr (someSymbol)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Void (Void, absurd)
import Data.Word (Word64)
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.Debug (ExtImpl, CommandExt)
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.LLVM.MemModel qualified as Mem
import Lang.Crucible.Pretty (IntrinsicPrinters, ppRegVal)
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator.GlobalState qualified as C
import Lang.Crucible.Simulator.RegMap qualified as C
import Numeric (showHex)
import Prettyprinter as PP
import What4.Interface qualified as W4

-- | Helper, not exported
regNames ::
  M.PrettyF (M.ArchReg arch) =>
  M.GenArchVals mem arch ->
  Ctx.Assignment (Const String) (M.MacawCrucibleRegTypes arch)
regNames archVals =
  M.macawAssignToCruc
    (Const . show . M.prettyF)
    (M.crucGenRegAssignment (M.archFunctions archVals))

data MacawCommand
  = MDwarfGlobals
  | MMem
  | MRegister
  | MTrace
  | MSloc
  deriving (Bounded, Enum)

instance PP.Pretty MacawCommand where
  pretty = PP.pretty . name

abbrev :: MacawCommand -> Text
abbrev =
  \case
    MDwarfGlobals -> "mglob"
    MMem -> "mmem"
    MRegister -> "mreg"
    MTrace -> "mtr"
    MSloc -> "sl"

detail :: MacawCommand -> Maybe Text
detail =
  \case
    MDwarfGlobals -> Just "\
      \When given no arguments, prints all globals described in DWARF. \
      \Otherwise, prints the globals with the given names, one per line.\
      \"
    MMem -> Nothing
    MRegister -> Just "\
      \When given no arguments, prints all machine registers. \
      \Otherwise, prints the registers with the given names, one per line.\
      \\n\n\

      \The values printed may be slightly out of date. \
      \See https://github.com/GaloisInc/macaw/issues/460 for a discussion.\
      \"
    MTrace -> Just "\
      \Prints the machine instructions in the N most recent basic blocks.\
      \The default value for N is 2.\
      \The trace does not include any overrides that may have been executed.\
      \It will be empty for S-expression programs.\
      \"
    MSloc -> Just "\
      \Prints the current source location (file, line, column) and function name \
      \from DWARF debug information. Requires the binary to be compiled with debug info (-g).\
      \"

help :: MacawCommand -> Text
help =
  \case
    MDwarfGlobals -> "Print DWARF globals"
    MMem -> "Display LLVM memory"
    MRegister -> "Display machine registers"
    MTrace -> "Print executed machine instructions"
    MSloc -> "Print current source location"

name :: MacawCommand -> Text
name =
  \case
    MDwarfGlobals -> "mglobals"
    MMem -> "mmemory"
    MRegister -> "mregister"
    MTrace -> "mtrace"
    MSloc -> "sloc"

rMDwarfGlobals :: Debug.RegexRepr Debug.ArgTypeRepr (Debug.Star Debug.Text)
rMDwarfGlobals = knownRepr

rMemory :: Debug.RegexRepr Debug.ArgTypeRepr Debug.Empty
rMemory = knownRepr

rMRegister :: Debug.RegexRepr Debug.ArgTypeRepr (Debug.Star Debug.Text)
rMRegister = knownRepr

rMTrace :: Debug.RegexRepr Debug.ArgTypeRepr (Debug.Empty Debug.:| Debug.Int)
rMTrace = knownRepr

rMSloc :: Debug.RegexRepr Debug.ArgTypeRepr Debug.Empty
rMSloc = knownRepr

enumRepr :: [Text] -> Some (Debug.RegexRepr Debug.ArgTypeRepr)
enumRepr =
  \case
    [] -> Some Debug.Fail
    (opt : opts) ->
      case (someSymbol opt, enumRepr opts) of
        (Some s, Some rest) ->
          Some (Debug.Or (Debug.Lit (Debug.TExactlyRepr s)) rest)

-- | We use a runtime-computed regex here to offer better completion and
-- highlighting for register names, but 'rMRegister' is more permissive.
regex ::
  M.PrettyF (M.ArchReg arch) =>
  M.GenArchVals mem arch ->
  MacawCommand ->
  Some (Debug.RegexRepr Debug.ArgTypeRepr)
regex archVals =
  \case
    MDwarfGlobals -> Some rMDwarfGlobals
    MMem -> Some rMemory
    MRegister ->
      case enumRepr (M.toListFC (Text.pack . getConst) (regNames archVals)) of
        Some r -> Some (Debug.Star r)
    MTrace -> Some rMTrace
    MSloc -> Some rMSloc

macawCommandExt ::
  M.PrettyF (M.ArchReg arch) =>
  M.GenArchVals mem arch ->
  CommandExt MacawCommand
macawCommandExt archVals =
  Debug.CommandExt
  { Debug.extAbbrev = abbrev
  , Debug.extDetail = detail
  , Debug.extHelp = help
  , Debug.extList = [minBound..maxBound]
  , Debug.extName = name
  , Debug.extRegex = regex archVals
  }

data MacawResponse
  = RMemory (PP.Doc Void)
  | RMDwarfGlobals [String] [(ByteString, PP.Doc Void)]
  | RMissingMemory
  | RMRegister [(String, PP.Doc Void)]
  | RMTrace [[Text]]
  | RNoRegs
  | RSourceLoc (Maybe SourceLocation)
  | RNoSourceInfo

instance PP.Pretty MacawResponse where
  pretty =
    \case
      RMemory mem -> fmap absurd mem
      RMissingMemory -> "LLVM memory global variable was undefined!"
      RNoRegs -> "Couldn't find register struct"
      RMDwarfGlobals errs globals ->
        let warnings = if List.null errs
                       then PP.emptyDoc
                       else "Warnings while processing DWARF: " <> PP.line <> (PP.indent 4 $ PP.align (PP.vsep $ List.map PP.pretty errs))
            globalDocs = List.map
                (\(nm, d) -> PP.pretty (Text.decodeUtf8Lenient nm) PP.<> ":" PP.<+> PP.align (fmap absurd d))
                globals
        -- TODO(#468): replace the pretty-printing of globals inherited from Data.Macaw.Dwarf with more user-friendly output
        in if List.null errs && List.null globals
           then PP.emptyDoc
           else PP.vsep (warnings : globalDocs)
      RMRegister regs ->
        PP.vsep $
          List.map
            (\(nm, d) -> PP.pretty nm PP.<> ":" PP.<+> PP.align (fmap absurd d))
            regs
      RMTrace t ->
        if List.null t || all List.null t
        then PP.emptyDoc
        else PP.vcat (PP.punctuate PP.line (map (PP.vcat . map PP.pretty) t))
      RSourceLoc Nothing ->
        "Source location not found for current PC (may be outside compiled code or PC is symbolic)"
      RSourceLoc (Just loc) ->
        let functionLine = case slFunction loc of
              Just fn -> ["  Function: " PP.<> PP.pretty (Text.decodeUtf8Lenient fn)]
              Nothing -> []
        in PP.vcat $
          [ "Source location:"
          , "  File:    " PP.<> PP.pretty (Text.decodeUtf8Lenient (slFile loc))
          , "  Line:    " PP.<> PP.pretty (slLine loc)
          , "  Column:  " PP.<> PP.pretty (slColumn loc)
          ] ++ functionLine ++
          [ "  Address: 0x" PP.<> PP.pretty (showHex (slAddress loc) "")
          ]
      RNoSourceInfo ->
        "No DWARF line information available (binary not compiled with -g)"

type instance Debug.ResponseExt MacawCommand = MacawResponse

-- | Helper, not exported
insnsInStmts :: C.StmtSeq (M.MacawExt arch) blocks ret args -> [Text]
insnsInStmts =
  \case
    C.ConsStmt _loc s rest ->
      case s of
        C.ExtendAssign (M.MacawInstructionStart _ _ disasm) ->
          disasm : insnsInStmts rest
        _ -> insnsInStmts rest
    C.TermStmt {} -> []

-- | Helper, not exported
ppRegs ::
  M.PrettyF (M.ArchReg arch) =>
  W4.IsExpr (W4.SymExpr sym) =>
  IntrinsicPrinters sym ->
  M.GenArchVals mem arch ->
  -- | Print only registers with these names
  [Text] ->
  C.RegValue sym (C.StructType (M.MacawCrucibleRegTypes arch)) ->
  [(String, PP.Doc ann)]
ppRegs iFns archVals nms regs =
  Maybe.catMaybes $
    M.toListFC
      (\(Pair (Const nm) (Pair t v)) ->
        if List.null nms || Text.pack nm `List.elem` nms
        then Just (nm, ppRegVal iFns t v)
        else Nothing)
      (Ctx.zipWith Pair (regNames archVals) (Ctx.zipWith Pair regTypes regs))
  where
    regTypes = M.crucArchRegTypes (M.archFunctions archVals)

-- | Helper, not exported
ppGlobals ::
  -- | Print only globals with these names
  --
  -- Expected to be short, because it comes from the user. So, no need for a `Set`.
  [Text] ->
  [D.Variable] ->
  [(ByteString, PP.Doc ann)]
ppGlobals nms =
  -- Assuming the compiler has UTF-8 encoded the names of globals in the DWARF
  let bsNms = map Text.encodeUtf8 nms in
  Maybe.mapMaybe $ \var ->
    let nm = D.nameVal . D.varName $ var in
    if List.null nms || List.elem nm bsNms
    then Just (nm, PP.pretty var)
    else Nothing

-- | Extract the program counter from register state.
-- Returns Nothing if the PC cannot be determined (e.g., symbolic value).
extractProgramCounter ::
  forall arch sym mem.
  M.RegisterInfo (M.ArchReg arch) =>
  M.MemWidth (M.ArchAddrWidth arch) =>
  W4.IsExpr (W4.SymExpr sym) =>
  C.IsInterpretedFloatSymExprBuilder sym =>
  M.SymArchConstraints arch =>
  M.GenArchVals mem arch ->
  C.RegValue sym (C.StructType (M.MacawCrucibleRegTypes arch)) ->
  Maybe Word64
extractProgramCounter archVals regs =
  let regType = C.StructRepr (M.crucArchRegTypes (M.archFunctions archVals))
      regsEntry = C.RegEntry regType regs
      ipEntry = M.lookupReg archVals regsEntry M.ip_reg
      ipPtr = C.regValue ipEntry
      (_, ptrOffset) = Mem.llvmPointerView ipPtr
  in case W4.asBV ptrOffset of
       Just bv -> Just (fromInteger (BV.asUnsigned bv))
       Nothing -> Nothing

macawExtImpl ::
  M.PrettyF (M.ArchReg arch) =>
  M.RegisterInfo (M.ArchReg arch) =>
  OrdF (M.ArchReg arch) =>
  M.MemWidth (M.ArchAddrWidth arch) =>
  W4.IsExpr (W4.SymExpr sym) =>
  C.IsInterpretedFloatSymExprBuilder sym =>
  IntrinsicPrinters sym ->
  C.GlobalVar Mem.Mem ->
  M.GenArchVals mem arch ->
  Maybe (Elf.Elf (M.ArchAddrWidth arch)) ->
  Maybe DI.DwarfInfoCache ->
  ExtImpl MacawCommand p sym (M.MacawExt arch) t
macawExtImpl iFns mVar archVals mElf dwarfCache =
  -- Parse DWARF info for globals (still eager)
  let (errs, cus) = case mElf of
        Just elf -> D.dwarfInfoFromElf elf
        Nothing -> ([], [])

  in Debug.ExtImpl $
    \case
      MDwarfGlobals ->
        Debug.CommandImpl
        { Debug.implRegex = rMDwarfGlobals
        , Debug.implBody =
            let vars = D.dwarfGlobals cus in
            \ctx _execState (Debug.MStar gNms0) -> do
              let gNms = List.map (\(Debug.MLit (Debug.AText t)) -> t) gNms0
              let resp = Debug.XResponse (RMDwarfGlobals errs $ ppGlobals gNms vars)
              pure (Debug.EvalResult ctx C.ExecutionFeatureNoChange resp)
        }
      MMem ->
        Debug.CommandImpl
        { Debug.implRegex = rMemory
        , Debug.implBody =
            \ctx execState Debug.MEmpty -> do
              let result = Debug.EvalResult ctx C.ExecutionFeatureNoChange Debug.Ok
              case Debug.execStateSimState execState of
                Left notApplicable ->
                  pure result { Debug.evalResp = Debug.UserError (Debug.NotApplicable notApplicable) }
                Right (C.SomeSimState simState) -> do
                  let globs = simState Lens.^. C.stateTree . C.actFrame . C.gpGlobals
                  case C.lookupGlobal mVar globs of
                    Nothing -> pure result { Debug.evalResp = Debug.XResponse RMissingMemory }
                    Just mem ->
                      let resp = Debug.XResponse (RMemory (Mem.ppMem (Mem.memImplHeap mem))) in
                      pure result { Debug.evalResp = resp }
        }
      MRegister ->
        Debug.CommandImpl
        { Debug.implRegex = rMRegister
        , Debug.implBody =
            \ctx execState (Debug.MStar rNms0) -> do
              let rNms = List.map (\(Debug.MLit (Debug.AText t)) -> t) rNms0
              let resp =
                      case M.execStateRegs (M.archFunctions archVals) execState of
                        Nothing -> Debug.XResponse RNoRegs
                        Just regs ->
                          Debug.XResponse
                            (RMRegister (ppRegs iFns archVals rNms regs))
              let result = Debug.EvalResult ctx C.ExecutionFeatureNoChange Debug.Ok
              pure result { Debug.evalResp = resp }
        }
      MTrace ->
        Debug.CommandImpl
        { Debug.implRegex = rMTrace
        , Debug.implBody =
            \ctx _execState m -> do
              let n =
                    case m of
                      Debug.MLeft Debug.MEmpty -> 2
                      Debug.MRight (Debug.MLit (Debug.AInt i)) -> i
              ents <- reverse <$> Debug.latest (Debug.dbgTrace ctx) n
              let entryInsns (Debug.TraceEntry cfg (Some blkId)) =
                    let blk = C.cfgBlockMap cfg Lens.^. ixF' (C.blockIDIndex blkId) in
                    insnsInStmts (C._blockStmts blk)
              let resp = Debug.XResponse (RMTrace (map entryInsns ents))
              pure (Debug.EvalResult ctx C.ExecutionFeatureNoChange resp)
        }
      MSloc ->
        Debug.CommandImpl
        { Debug.implRegex = rMSloc
        , Debug.implBody =
            \ctx execState Debug.MEmpty -> do
              let result = Debug.EvalResult ctx C.ExecutionFeatureNoChange Debug.Ok

              case dwarfCache of
                Nothing ->
                  pure result { Debug.evalResp = Debug.XResponse RNoSourceInfo }
                Just cache -> do
                  case M.execStateRegs (M.archFunctions archVals) execState of
                    Nothing ->
                      pure result { Debug.evalResp = Debug.XResponse RNoRegs }
                    Just regs ->
                      M.withArchConstraints archVals $
                        case extractProgramCounter archVals regs of
                          Nothing ->
                            -- PC is symbolic or not found
                            pure result { Debug.evalResp = Debug.XResponse (RSourceLoc Nothing) }
                          Just pc -> do
                            -- LAZY LOOKUP: Only builds maps for the CU containing pc
                            sourceLoc <- DI.lookupSourceLocation cache pc
                            let resp = Debug.XResponse (RSourceLoc sourceLoc)
                            pure result { Debug.evalResp = resp }
        }

