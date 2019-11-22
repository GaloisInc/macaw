{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

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
import           Data.Macaw.CFG ( ArchAddrWidth )
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory.ElfLoader as ML
import           Data.Macaw.PPC
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.Refinement as MR
import           Data.Macaw.Symbolic ( SymArchConstraints )
import qualified Data.Macaw.X86 as MX86
import           Data.Macaw.X86.Symbolic ()
import qualified Data.Map as M
import           Data.Maybe
import           Data.Monoid
import           Data.Parameterized.Some
import           Data.Semigroup
import           Data.Semigroup ()
import qualified Data.Text.IO as TIO
import           Data.Text.Prettyprint.Doc
import qualified Lang.Crucible.Backend.Online as CBO
import           GHC.TypeLits
import qualified Options.Applicative as O
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import           System.Exit
import qualified What4.Expr as WE
import qualified Data.Parameterized.Nonce as PN

import           Prelude

data Options = Options { inputFile :: FilePath
                       , unrefined :: Bool
                       , summaryOnly :: Bool
                       , verbose :: Bool
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
                            , 16 <= ArchAddrWidth arch
                            , MonadIO m) =>
                            Options
                         -> (MD.DiscoveryState arch -> m a)
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
  di <- liftIO $ if unrefined opts
                 then return $ MD.cfgFromAddrs arch_info (memoryImage bin) M.empty entries []
                 else AI.withArchConstraints arch_info $ do
    CBO.withYicesOnlineBackend WE.FloatUninterpretedRepr PN.globalNonceGenerator CBO.NoUnsatFeatures $ \sym -> do
      ctx <- MR.defaultRefinementContext sym bin
      MR.cfgFromAddrs ctx arch_info (memoryImage bin) M.empty entries []
  f di

showDiscoveryInfo opts di = do
  unless (summaryOnly opts) $
    if verbose opts then showDetails di else showOverview di
  showSummary di

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

showSummary di =
  let summarizeBlock (_blkAddr, pblk) s =
        let s' = case MD.pblockTermStmt pblk of
                   MD.ParsedTranslateError _ ->
                     s { blockTranslateErrors = blockTranslateErrors s + 1 }
                   MD.ClassifyFailure {} ->
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
            blksSummary = foldr summarizeBlock funcSummary blks
            funcErrs = foldr (\a v -> a blksSummary + v) 0 [ blockTranslateErrors, blockUnknownTargetErrors ]
        in (mappend s blksSummary)
           { functionsWithErrors = functionsWithErrors s + funcErrs
           }
      summarize = vcat [ pretty ":: ==== SUMMARY ===="
                       , pretty $ foldr summarizeFunction mempty (di ^. MD.funInfo .to M.toList)
                       ]
  in putStrLn $ show $ summarize

showOverview di =
  let getIssue (blkAddr, pblk) =
        let issue = case MD.pblockTermStmt pblk of
              MD.ParsedTranslateError r -> pretty "Translation failure:" <+> pretty (show r)
              MD.ClassifyFailure {} -> pretty "Classify failure"
              _ -> emptyDoc
        in hsep [ pretty "Block @", pretty $ show blkAddr, issue ]
      funcSummary (funAddr, (Some dfi)) =
        let blkSummary = map getIssue (dfi ^. MD.parsedBlocks . to M.toList)
        in vcat [ pretty "Function @" <+> pretty (show funAddr)
                , indent 2 $ vcat blkSummary
                ]
  in putStrLn $ show $ vcat $ map funcSummary (di ^. MD.funInfo .to M.toList)

showDetails di =
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
