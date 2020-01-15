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

import           Control.Lens ( (^.) )
import qualified Control.Lens as L
import           Control.Monad ( unless, forM_ )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Refinement as MR
import           Data.Macaw.Symbolic ( SymArchConstraints )
import qualified Data.Map as M
import           Data.Maybe ( isNothing )
import           Data.Monoid
import           Data.Parameterized.Some
import qualified Data.Text.IO as TIO
import           Data.Text.Prettyprint.Doc as PP
import qualified Options.Applicative as O

import           Prelude

import           Initialization ( withElf, withRefinedDiscovery )
import           Options( Options(..) )
import           Summary

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
                <*> O.option O.auto ( O.metavar "NAT"
                                    <> O.help "The number of seconds to wait for the solver before timing out"
                                    <> O.value (MR.timeoutSeconds MR.defaultRefinementConfig)
                                    <> O.long "timeout"
                                    <> O.short 't'
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
  withElf opts $ \archInfo bin unrefinedDI -> do
    case unrefined opts of
      True -> showDiscoveryInfo opts unrefinedDI Nothing
      False ->
        withRefinedDiscovery opts archInfo bin $ \refinedDI refinedInfo -> do
          showDiscoveryInfo opts unrefinedDI (Just (refinedDI, refinedInfo))

showDiscoveryInfo :: (SymArchConstraints arch)
                  => Options
                  -> MD.DiscoveryState arch
                  -> Maybe (MD.DiscoveryState arch, MR.RefinementInfo arch)
                  -> IO ()
showDiscoveryInfo opts unrefinedDI mrefinedDI = do
  unless (summaryOnly opts) $ do
    if verbose opts
      then showDetails unrefinedDI mrefinedDI
      else showOverview unrefinedDI mrefinedDI

  showSummary unrefinedDI mrefinedDI



showSummary :: forall arch . (MC.MemWidth (MC.ArchAddrWidth arch)) => MD.DiscoveryState arch -> Maybe (MD.DiscoveryState arch, MR.RefinementInfo arch) -> IO ()
showSummary unrefinedDI mdirefined =
  let summarize di = vcat [ pretty ":: ==== SUMMARY ===="
                          , pretty (summarizeInfo di)
                          ]
  in case mdirefined of
    Nothing -> putStrLn (show (summarize unrefinedDI))
    Just (refinedDI, rinfo) -> do
      let lhs = PP.vcat [ PP.pretty "Unrefined"
                        , summarize unrefinedDI
                        ]
      let rhs = PP.vcat [ PP.pretty "Refined"
                        , PP.nest 4 (summarizeRefinementInfo rinfo)
                        , summarize refinedDI
                        ]
      putStrLn (show (PP.vsep [ lhs, rhs ]))

showOverview :: (MC.MemWidth (MC.ArchAddrWidth arch))
             => MD.DiscoveryState arch
             -> Maybe (MD.DiscoveryState arch, MR.RefinementInfo arch)
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
        let blkSummary = map (getIssue dfi) (dfi ^. MD.parsedBlocks . L.to M.toList)
        in vcat [ pretty "Function @" <+> pretty (show funAddr)
                , indent 2 $ vcat blkSummary
                ]
      summaries di = map funcSummary (di ^. MD.funInfo . L.to M.toList)
  in case mrefinedDI of
    Nothing -> putStrLn (show (PP.vcat (summaries unrefinedDI)))
    Just (refinedDI, rinfo) -> do
      let lhs = PP.vcat ( PP.pretty "Unrefined"
                        : PP.pretty "========="
                        : summaries unrefinedDI
                        )
      let rhs = PP.vcat ( PP.pretty "Refined"
                        : PP.pretty "======="
                        : PP.nest 4 (summarizeRefinementInfo rinfo)
                        : summaries refinedDI
                        )
      putStrLn (show (PP.vsep [ lhs, rhs ]))

summarizeRefinementInfo :: (MC.MemWidth (MC.ArchAddrWidth arch)) => MR.RefinementInfo arch -> PP.Doc a
summarizeRefinementInfo rinfo =
  PP.vcat [ PP.pretty "Timeouts: " <> PP.list (fmap (PP.pretty . show) (MR.refinementTimeouts rinfo))
          , PP.pretty "Spurious: " <> PP.list (fmap (PP.pretty . show) (MR.refinementSpurious rinfo))
          , PP.pretty "No Models: " <> PP.list (fmap (PP.pretty . show) (MR.refinementNoModels rinfo))
          , PP.pretty "Errors: " <> PP.list (fmap (PP.pretty . show) (MR.refinementErrors rinfo))
          ]

showDetails :: (SymArchConstraints arch)
            => MD.DiscoveryState arch
            -> Maybe (MD.DiscoveryState arch, MR.RefinementInfo arch)
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
