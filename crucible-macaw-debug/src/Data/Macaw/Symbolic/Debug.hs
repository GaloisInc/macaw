{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Symbolic.Debug
  ( macawCommandExt
  , macawExtImpl
  ) where

import Control.Lens qualified as Lens
import Data.ByteString (ByteString)
import Data.ElfEdit qualified as Elf
import Data.Functor.Const (Const(Const, getConst))
import Data.Functor.Product (Product(Pair))
import Data.List qualified as List
import Data.Macaw.Dwarf qualified as D
import Data.Macaw.CFG qualified as M
import Data.Macaw.Symbolic qualified as M
import Data.Macaw.Symbolic.Regs qualified as M
import Data.Maybe qualified as Maybe
import Data.Parameterized.Classes (knownRepr, ixF')
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(Some))
import Data.Parameterized.SymbolRepr (someSymbol)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text (Text)
import Data.Void (Void, absurd)
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.Debug (ExtImpl, CommandExt)
import Lang.Crucible.Debug qualified as Debug
import Lang.Crucible.Pretty (IntrinsicPrinters, ppRegVal)
import Lang.Crucible.Simulator.EvalStmt qualified as C
import Lang.Crucible.Simulator.RegMap qualified as C
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
  | MRegister
  | MTrace
  deriving (Bounded, Enum)

instance PP.Pretty MacawCommand where
  pretty = PP.pretty . name

abbrev :: MacawCommand -> Text
abbrev =
  \case
    MDwarfGlobals -> "mglob"
    MRegister -> "mreg"
    MTrace -> "mtr"

detail :: MacawCommand -> Maybe Text
detail =
  \case
    MDwarfGlobals -> Just "\
      \When given no arguments, prints all globals described in DWARF. \
      \Otherwise, prints the globals with the given names, one per line.\
      \"
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

help :: MacawCommand -> Text
help =
  \case
    MDwarfGlobals -> "print DWARF globals"
    MRegister -> "display machine registers"
    MTrace -> "print executed machine instructions"

name :: MacawCommand -> Text
name =
  \case
    MDwarfGlobals -> "mglobals"
    MRegister -> "mregister"
    MTrace -> "mtrace"

rMDwarfGlobals :: Debug.RegexRepr Debug.ArgTypeRepr (Debug.Star Debug.Text)
rMDwarfGlobals = knownRepr

rMRegister :: Debug.RegexRepr Debug.ArgTypeRepr (Debug.Star Debug.Text)
rMRegister = knownRepr

rMTrace :: Debug.RegexRepr Debug.ArgTypeRepr (Debug.Empty Debug.:| Debug.Int)
rMTrace = knownRepr

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
    MRegister ->
      case enumRepr (M.toListFC (Text.pack . getConst) (regNames archVals)) of
        Some r -> Some (Debug.Star r)
    MTrace -> Some rMTrace

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
  = RNoRegs
  | RMDwarfGlobals [String] [(ByteString, PP.Doc Void)]
  | RMRegister [(String, PP.Doc Void)]
  | RMTrace [[Text]]

instance PP.Pretty MacawResponse where
  pretty =
    \case
      RNoRegs -> "Couldn't find register struct"
      RMDwarfGlobals errs globals ->
        let warnings = if List.null errs
                       then PP.emptyDoc
                       else "Warnings while processing DWARF: " <> PP.line <> (PP.indent 4 $ PP.align (PP.vsep $ List.map PP.pretty errs))
        -- TODO(#468): replace the pretty-printing of globals inherited from Data.Macaw.Dwarf with more user-friendly output
        in PP.vsep $
           (warnings :) $
             List.map
                (\(nm, d) -> PP.pretty (Text.decodeUtf8Lenient nm) PP.<> ":" PP.<+> PP.align (fmap absurd d))
                globals
      RMRegister regs ->
        PP.vsep $
          List.map
            (\(nm, d) -> PP.pretty nm PP.<> ":" PP.<+> PP.align (fmap absurd d))
            regs
      RMTrace t -> PP.vcat (PP.punctuate PP.line (map (PP.vcat . map PP.pretty) t))

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

macawExtImpl ::
  M.PrettyF (M.ArchReg arch) =>
  W4.IsExpr (W4.SymExpr sym) =>
  IntrinsicPrinters sym ->
  M.GenArchVals mem arch ->
  Maybe (Elf.Elf (M.ArchAddrWidth arch)) ->
  ExtImpl MacawCommand p sym (M.MacawExt arch) t
macawExtImpl iFns archVals mElf =
  Debug.ExtImpl $
    \case
      MDwarfGlobals ->
        Debug.CommandImpl
        { Debug.implRegex = rMDwarfGlobals
        , Debug.implBody =
            let (errs, cus) =
                  case mElf of
                    Just elf -> D.dwarfInfoFromElf elf
                    Nothing -> ([],[]) in
            let vars = D.dwarfGlobals cus in
            \ctx _execState (Debug.MStar gNms0) -> do
              let gNms = List.map (\(Debug.MLit (Debug.AText t)) -> t) gNms0
              let resp = Debug.XResponse (RMDwarfGlobals errs $ ppGlobals gNms vars)
              pure (Debug.EvalResult ctx C.ExecutionFeatureNoChange resp)
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

