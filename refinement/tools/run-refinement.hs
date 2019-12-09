{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Main ( main ) where

import           Control.Lens
import           Control.Monad
import qualified Control.Monad.Catch as X
import           Control.Monad.IO.Class
import           Data.Bits ( (.|.) )
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as E
import           Data.Foldable
import qualified Data.Macaw.Architecture.Info as AI
import           Data.Macaw.BinaryLoader as MBL
import           Data.Macaw.BinaryLoader.X86 ()
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory.ElfLoader as ML
import           Data.Macaw.PPC
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.Refinement as MR
import           Data.Macaw.Symbolic ( SymArchConstraints )
import qualified Data.Macaw.X86 as MX86
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Map as M
import           Data.Maybe ( isNothing, catMaybes )
import           Data.Monoid
import           Data.Parameterized.Some
import           Data.Proxy ( Proxy(..) )
import           Data.Semigroup
import           Data.Semigroup ()
import qualified Data.Text.IO as TIO
import           Data.Text.Prettyprint.Doc as PP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Simple as CBS
import           GHC.TypeLits
import qualified Options.Applicative as O
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import           System.Exit
import qualified What4.Config as WC
import qualified What4.Expr as WE
import qualified What4.Interface as WI
import qualified Data.Parameterized.Nonce as PN
import qualified What4.ProblemFeatures as WPF
import qualified What4.Solver.CVC4 as WSC
import qualified What4.Solver.Yices as WSY
import qualified What4.Solver.Z3 as WSZ
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTLib2 as WPS

import           Prelude

data Solver = CVC4 | Yices | Z3
  deriving (Read, Show, Eq, Ord)

data Options = Options { inputFile :: FilePath
                       , unrefined :: Bool
                       , summaryOnly :: Bool
                       , verbose :: Bool
                       , solver :: Solver
                       }

optionsParser :: O.Parser Options
optionsParser = Options
                <$> O.strArgument ( O.metavar "FILE"
                                    <> O.help "The binary ELF file to perform discovery on"
                                  )
                <*> O.switch ( O.long "unrefined"
                             <> O.short 'u'
                             <> O.help "No refinement of discovery results"
                             )
                <*> O.switch ( O.long "summary"
                             <> O.short 's'
                             <> O.help "Only show summary of discovery/refinement.\n\
                                       \Without this flag a full list of all discovered\n\
                                       \functions and blocks is output."
                             )
                <*> O.switch ( O.long "verbose"
                             <> O.short 'v'
                             <> O.help "Show verbose information about each discovered\n\
                                       \function and block."
                                       )
                <*> O.option O.auto ( O.metavar "SOLVER"
                                   <> O.help "The SMT solver to use"
                                   <> O.short 'S'
                                   <> O.long "solver"
                                   <> O.value Yices
                                    )

main :: IO ()
main = O.execParser optParser >>= doRefinement
  where optParser = O.info ( optionsParser O.<**> O.helper )
                    ( O.fullDesc
                    <> O.progDesc "A tool to show refined code discovery for ELF binaries"
                    <> O.header "run-refinement - code discovery output"
                    )

doRefinement :: Options -> IO ()
doRefinement opts = do
  let filename = inputFile opts
  bs <- BS.readFile filename
  case E.parseElf bs of
      E.Elf64Res warnings elf -> mapM_ print warnings >> withElf64 elf
      E.Elf32Res warnings elf -> mapM_ print warnings >> withElf32 elf
      _ -> die "not a 64-bit ELF file"
  where
    withElf64 elf =
      case E.elfMachine elf of
        E.EM_PPC64 -> do
          bin <- MBL.loadBinary @PPC64.PPC ML.defaultLoadOptions elf
          let pli = ppc64_linux_info bin
          withBinaryDiscoveredInfo opts (showDiscoveryInfo opts) pli bin
        E.EM_X86_64 ->
          withBinaryDiscoveredInfo opts (showDiscoveryInfo opts) MX86.x86_64_linux_info =<<
            MBL.loadBinary @MX86.X86_64 ML.defaultLoadOptions elf
        m -> error $ "only X86 and PPC64 supported for 64-bit analysis; no support for " ++ show m
    withElf32 elf =
      case E.elfMachine elf of
        E.EM_PPC -> do  -- 32 bit
          bin <- MBL.loadBinary @PPC32.PPC ML.defaultLoadOptions elf
          let pli = ppc32_linux_info bin
          withBinaryDiscoveredInfo opts (showDiscoveryInfo opts) pli bin
        m -> error $ "only PPC supported for 32-bit analysis; no support for " ++ show m

withNewBackend :: (MonadIO m)
               => Solver
               -> (forall proxy t solver fs sym . (sym ~ CBS.SimpleBackend t fs, CB.IsSymInterface sym, WPO.OnlineSolver t solver) => proxy solver -> WPF.ProblemFeatures -> sym -> m a)
               -> m a
withNewBackend s k = do
  sym :: CBS.SimpleBackend PN.GlobalNonceGenerator (WE.Flags WE.FloatUninterpreted)
      <- liftIO $ CBS.newSimpleBackend WE.FloatUninterpretedRepr PN.globalNonceGenerator
  case s of
    CVC4 -> do
      let proxy = Proxy @(WPS.Writer WSC.CVC4)
      liftIO $ WC.extendConfig WSC.cvc4Options (WI.getConfiguration sym)
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useNonlinearArithmetic
      k proxy features sym
    Yices -> do
      let proxy = Proxy @(WSY.Connection PN.GlobalNonceGenerator)
      liftIO $ WC.extendConfig WSY.yicesOptions (WI.getConfiguration sym)
      -- For some reason, non-linear arithmetic is required for cvc4 and z3 but doesn't work at all with yices
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs
      k proxy features sym
    Z3 -> do
      let proxy = Proxy @(WPS.Writer WSZ.Z3)
      liftIO $ WC.extendConfig WSZ.z3Options (WI.getConfiguration sym)
      let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs .|. WPF.useNonlinearArithmetic
      k proxy features sym

withBinaryDiscoveredInfo :: ( X.MonadThrow m
                            , MBL.BinaryLoader arch binFmt
                            , SymArchConstraints arch
                            , 16 <= MC.ArchAddrWidth arch
                            , MonadIO m) =>
                            Options
                         -> (MD.DiscoveryState arch -> Maybe (MD.DiscoveryState arch) -> m a)
                         -> AI.ArchitectureInfo arch
                         -> MBL.LoadedBinary arch binFmt
                         -> m a
withBinaryDiscoveredInfo opts f arch_info bin = do
  entries <- toList <$> entryPoints bin
  when (verbose opts) $
    liftIO $ do putStr "Entrypoints: "
                putStrLn $ show $ fmap show entries
                -- putStrLn $ show (fmap (show . MM.segoffSegment) entries)
                -- putStrLn $ show (fmap (show . MM.segoffOffset) entries)
  let unrefinedDI = MD.cfgFromAddrs arch_info (memoryImage bin) M.empty entries []
  mrefinedDI <- case unrefined opts of
    True -> return Nothing
    False -> AI.withArchConstraints arch_info $ liftIO $ do
      withNewBackend (solver opts) $ \proxy features sym -> do
        ctx <- MR.defaultRefinementContext features sym bin
        Just <$> MR.cfgFromAddrs proxy ctx arch_info (memoryImage bin) M.empty entries []
  f unrefinedDI mrefinedDI

showDiscoveryInfo :: (SymArchConstraints arch)
                  => Options
                  -> MD.DiscoveryState arch
                  -> Maybe (MD.DiscoveryState arch)
                  -> IO ()
showDiscoveryInfo opts unrefinedDI mrefinedDI = do
  unless (summaryOnly opts) $ do
    if verbose opts
      then showDetails unrefinedDI mrefinedDI
      else showOverview unrefinedDI mrefinedDI

  showSummary unrefinedDI mrefinedDI

data Summary = Summary { functionCnt :: Int
                       , functionsWithErrors :: Int
                       , blockCnt :: Int
                       , blockTranslateErrors :: Int
                       , blockUnknownTargetErrors :: Int -- ClassifyFailure
                       , maxBlocksPerFunction :: Int
                       }

instance Semigroup Summary where
  a <> b =
    Summary { functionCnt = functionCnt a + functionCnt b
            , functionsWithErrors = functionsWithErrors a + functionsWithErrors b
            , blockCnt = blockCnt a + blockCnt b
            , blockTranslateErrors = blockTranslateErrors a + blockTranslateErrors b
            , blockUnknownTargetErrors = blockUnknownTargetErrors a + blockUnknownTargetErrors b
            , maxBlocksPerFunction = max (maxBlocksPerFunction a) (maxBlocksPerFunction b)
            }

instance Monoid Summary where
  mempty = Summary 0 0 0 0 0 0

instance Pretty Summary where
  pretty s = vcat $ catMaybes
    [ Just $ pretty ":: Function count =" <+> pretty (show $ functionCnt s)
    , if functionsWithErrors s > 0
      then Just $ pretty "::    with errors =" <+> pretty (show $ functionsWithErrors s)
      else Nothing
    , Just $ pretty ":: Total block count =" <+> pretty (show $ blockCnt s)
    , Just $ pretty ":: Max blocks/function =" <+> pretty (show $ maxBlocksPerFunction s)
    , if blockTranslateErrors s > 0
      then Just (pretty "::  blocks with Translate errors (disassembly) =" <+>
                 pretty (show $ blockTranslateErrors s))
      else Nothing
    , if blockUnknownTargetErrors s > 0
      then Just (pretty "::  blocks with Classification/Unknown Target errors (discovery) =" <+>
                 pretty (show $ blockUnknownTargetErrors s))
      else Nothing
    ]

showSummary :: forall arch . MD.DiscoveryState arch -> Maybe (MD.DiscoveryState arch) -> IO ()
showSummary unrefinedDI mdirefined =
  let summarizeBlock :: MD.DiscoveryFunInfo arch ids
                     -> (a, MD.ParsedBlock arch ids)
                     -> Summary
                     -> Summary
      summarizeBlock dfi (_blkAddr, pblk) s =
        let s' = case MD.pblockTermStmt pblk of
                   MD.ParsedTranslateError _ ->
                     s { blockTranslateErrors = blockTranslateErrors s + 1 }
                   MD.ClassifyFailure {}
                     | isNothing (lookup (MD.pblockAddr pblk) (MD.discoveredClassifyFailureResolutions dfi)) ->
                       s { blockUnknownTargetErrors = blockUnknownTargetErrors s + 1 }
                   _ -> s
        in s'
      summarizeFunction (_funAddr, (Some dfi)) s =
        let funcSummary = mempty { functionCnt = 1
                                 , blockCnt = numBlks
                                 , maxBlocksPerFunction = numBlks
                                 }
            blks = (dfi ^. MD.parsedBlocks . to M.toList)
            numBlks = length blks
            blksSummary = foldr (summarizeBlock dfi) funcSummary blks
            funcErrs = foldr (\a v -> a blksSummary + v) 0 [ blockTranslateErrors, blockUnknownTargetErrors ]
        in (mappend s blksSummary)
           { functionsWithErrors = functionsWithErrors s + funcErrs
           }
      summarize di = vcat [ pretty ":: ==== SUMMARY ===="
                          , pretty $ foldr summarizeFunction mempty (di ^. MD.funInfo .to M.toList)
                          ]
  in case mdirefined of
    Nothing -> putStrLn (show (summarize unrefinedDI))
    Just refinedDI -> do
      let lhs = PP.vcat [ PP.pretty "Unrefined"
                        , summarize unrefinedDI
                        ]
      let rhs = PP.vcat [ PP.pretty "Refined"
                        , summarize refinedDI
                        ]
      putStrLn (show (PP.vsep [ lhs, rhs ]))

showOverview :: (MC.MemWidth (MC.ArchAddrWidth arch))
             => MD.DiscoveryState arch
             -> Maybe (MD.DiscoveryState arch)
             -> IO ()
showOverview unrefinedDI mrefinedDI =
  let getIssue dfi (blkAddr, pblk) =
        let issue = case MD.pblockTermStmt pblk of
              MD.ParsedTranslateError r -> pretty "Translation failure:" <+> pretty (show r)
              MD.ClassifyFailure _ rsns
                | isNothing (lookup (MD.pblockAddr pblk) (MD.discoveredClassifyFailureResolutions dfi)) ->
                  PP.vcat [ PP.pretty "Classify failure: "
                          , PP.nest 4 (PP.vcat (map PP.pretty rsns))
                          ]
              _ -> emptyDoc
        in hsep [ pretty "Block @", pretty $ show blkAddr, issue ]
      funcSummary (funAddr, (Some dfi)) =
        let blkSummary = map (getIssue dfi) (dfi ^. MD.parsedBlocks . to M.toList)
        in vcat [ pretty "Function @" <+> pretty (show funAddr)
                , indent 2 $ vcat blkSummary
                ]
      summaries di = map funcSummary (di ^. MD.funInfo . to M.toList)
  in case mrefinedDI of
    Nothing -> putStrLn (show (PP.vcat (summaries unrefinedDI)))
    Just refinedDI -> do
      let lhs = PP.vcat ( PP.pretty "Unrefined"
                        : PP.pretty "========="
                        : summaries unrefinedDI
                        )
      let rhs = PP.vcat ( PP.pretty "Refined"
                        : PP.pretty "======="
                        : summaries refinedDI
                        )
      putStrLn (show (PP.vsep [ lhs, rhs ]))

showDetails :: (SymArchConstraints arch)
            => MD.DiscoveryState arch
            -> Maybe (MD.DiscoveryState arch)
            -> IO ()
showDetails di _ =
  forM_ (M.toList (di ^. MD.funInfo)) $ \(funAddr, Some dfi) -> do
    putStrLn $ "===== BEGIN FUNCTION " ++ show funAddr ++ " ====="
    forM_ (M.toList (dfi ^. MD.parsedBlocks)) $ \(blockAddr, pb) -> do
      putStrLn $ "== begin block " ++ show blockAddr ++ " =="
      putStrLn . show $ MD.pblockStmts pb
      putStrLn ""
      case MD.pblockTermStmt pb of
        MD.ParsedTranslateError r -> do
          putStr "*** "
          putStr "TRANSLATE ERROR: "
          TIO.putStrLn r
        e@(MD.ClassifyFailure {}) -> do
          putStr "*** "
          putStr "CLASSIFY FAILURE: "
          putStrLn $ show e
        r -> do
          putStr "### block terminates with: "
          putStrLn $ show r
      putStrLn ""
    putStrLn ""
    putStrLn ""
