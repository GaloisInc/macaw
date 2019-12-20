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
import           Data.Maybe ( isNothing )
import           Data.Monoid
import           Data.Parameterized.Some
import qualified Data.Text.IO as TIO
import           Data.Text.Prettyprint.Doc as PP
import           GHC.TypeLits
import qualified Options.Applicative as O
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import           System.Exit

import           Prelude

import           Summary

data Options = Options { inputFile :: FilePath
                       , unrefined :: Bool
                       , summaryOnly :: Bool
                       , verbose :: Bool
                       , solver :: MR.Solver
                       , solverInteractionFile :: Maybe FilePath
                       , maximumModelCount :: Int
                       , threadCount :: Int
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
                                   <> O.value MR.Yices
                                    )
                <*> O.optional ( O.strOption ( O.metavar "FILE"
                                            <> O.long "solver-interaction-file"
                                            <> O.help "File to save solver interactions to"
                                             ))
                <*> O.option O.auto ( O.metavar "INT"
                                    <> O.help "The maximum number of models to consider valid for a given indirect call"
                                    <> O.value (MR.maximumModelCount MR.defaultRefinementConfig)
                                    <> O.long "maximum-model-count"
                                    <> O.short 'm'
                                    )
                <*> O.option O.auto ( O.metavar "NAT"
                                    <> O.help "The number of solver processes to run concurrently (minimum 1)"
                                    <> O.value 1
                                    <> O.short 'N'
                                    <> O.long "solver-processes"
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
      let config = MR.defaultRefinementConfig { MR.solver = solver opts
                                              , MR.solverInteractionFile = solverInteractionFile opts
                                              , MR.maximumModelCount = maximumModelCount opts
                                              , MR.parallelismFactor = min 1 (threadCount opts)
                                              }
      ctx <- MR.defaultRefinementContext config bin
      Just <$> MR.cfgFromAddrs ctx arch_info (memoryImage bin) M.empty entries []
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



showSummary :: forall arch . MD.DiscoveryState arch -> Maybe (MD.DiscoveryState arch) -> IO ()
showSummary unrefinedDI mdirefined =
  let summarize di = vcat [ pretty ":: ==== SUMMARY ===="
                          , pretty (summarizeInfo di)
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
