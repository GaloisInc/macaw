{-|
compare-dwarfdump generate dwarfdump-output on specific parts of binary,
and reports inconsistencies.

It currently only supports .eh_frame and .debug_frame sections.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wwarn #-}
module Main (main) where

import qualified Codec.Compression.Zlib as Zlib

import           Control.Exception
import           Control.Monad
import           Control.Monad.State
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString.Builder as Bld
import qualified Data.ByteString.Lazy as BSL
import           Data.Char
import qualified Data.ElfEdit as Elf
import qualified Data.ElfEdit.ByteString as Elf
import qualified Data.Map.Strict as Map
import           Data.String
import qualified Data.Vector as V
import           Data.Word
import           GHC.Stack
import           Numeric (showHex)
import           System.Directory
import           System.Environment
import           System.Exit
import           System.FilePath
import           System.IO
import qualified System.Process as P

import qualified Data.Dwarf as Dwarf

-- | @ppHex w v@ prints @v@ as hex with exactly w digits of output.
ppHex :: Int -> Word64 -> String
ppHex w x =
  let s = showHex x ""
      n = length s
   in replicate (w - n) '0' ++ drop (n-w) s

-- | Print a byte as two digit hex with upper case letters.
ppByte :: Word8 -> String
ppByte x | x < 16 = '0' : fmap toUpper (showHex x "")
         | otherwise = fmap toUpper (showHex x "")

-- | Monad for printing so we can capture output.
class Monad m => WriteMonad m where
  writeBuilder :: Bld.Builder -> m ()
  writeLn :: String -> m ()
  reportError :: HasCallStack => FilePath -> String -> m a

instance WriteMonad IO where
  writeBuilder l = Bld.hPutBuilder stdout l
  writeLn = putStrLn
  reportError path msg = hPutStrLn stderr (path <> ": " <> msg) >> exitFailure

-- | Pretty print instructions for a CIE or FDE.
ppInsns :: WriteMonad m
        => FilePath -- ^ File we are parsing
        -> BS.ByteString -- ^ .eh_frame/.debug_frame data
        -> Dwarf.DW_CIE -- ^ CIE for instructions
        -> Word64 -- ^ Offset for CIE/FDE
        -> Word64 -- ^ Size for CIE/FDE
        -> Dwarf.Encoding -- ^ Encoding of instructions
        -> BS.ByteString -- ^ Buffer for instructions
        -> m ()
ppInsns path ehFrameData cie off ctxSize enc insnBuf = do
  let tgtSize = Dwarf.cieTargetSize cie
  let end = Dwarf.cieEndianess cie
  let rdr = Dwarf.reader end enc tgtSize
  let ppCtx = Dwarf.CallFramePPCtx { Dwarf.ppDataAlignment = Dwarf.cieDataAlignmentFactor cie
                                   , Dwarf.ppReader = rdr
                                   , Dwarf.ppReg = Dwarf.ppX86CallFrameReg
                                   }
  case Dwarf.parseCallFrameInstructions end tgtSize insnBuf of
    Left (prev, insnOff, msg) -> do
      let ctxBytes = BS.take (fromIntegral ctxSize) $ BS.drop (fromIntegral off) ehFrameData
      reportError path
        $ ppHex 8 (fromIntegral off) <> " instruction parse failure.\n"
        <> "  Prev:\n"
        <> unlines ((\insn -> "    " <> Dwarf.ppCFA ppCtx insn) <$> prev)
        <> "  Message: " <> msg <> "\n"
        <> "  CIE Enc: " <> show (Dwarf.cieFdeEncoding cie) <> "\n"
        <> "  Offset:  " <> show insnOff <> "\n"
        <> "  Bytes:   " <> ppBuffer (BS.drop insnOff insnBuf) <> "\n"
        <> "  Context: " <> ppBuffer ctxBytes
    Right insns -> do
      forM_ insns $ \insn -> do
        writeBuilder "  "
        writeLn $ Dwarf.ppCFA ppCtx insn

-- | Information about .eh_frame/.debug_frame
data Frame = Frame { frameCtx :: !Dwarf.FrameContext
                     -- ^ Flag to indicate if this is .eh_frame or
                     -- .debug_frame.
                   , frameAddr :: !Word64
                     -- ^ Address frame is loaded at.
                   , frameData :: !BS.ByteString
                     -- ^ Bytes in frame
                   , frameExcept :: Maybe (Elf.Shdr BS.ByteString Word64)
                     -- ^ Section for .gcc_except_table if defined.
                     --
                     -- Used so we validate that we understand the
                     -- LSDA address.
                   }

ppEncoding :: Dwarf.Encoding -> String
ppEncoding Dwarf.Encoding32 = "DWARF32"
ppEncoding Dwarf.Encoding64 = "DWARF64"

-- | Print out all the FDEs for the given CIE in Dwarf dump format.
ppFDEs :: WriteMonad m
       => FilePath
       -> Frame
       -> Dwarf.DW_CIE -- ^ CIE for this FDE
       -> Word64 -- Offset within eh frame.
       -> m Dwarf.FDEParseError
ppFDEs path f cie off = do
  case Dwarf.getFDEAt (frameCtx f) (frameData f) cie off of
    Left e -> pure e
    Right (fde, off') -> do
      writeBuilder "\n"
      writeBuilder $ fromString $ ppHex 8 off
      writeBuilder " "
      writeBuilder $ fromString $ ppHex 8 (Dwarf.fdeSize fde)
      writeBuilder " "
      writeBuilder $ fromString $ ppHex 8 (Dwarf.fdeCiePointer fde)
      writeBuilder " FDE cie="
      writeBuilder $ fromString $ ppHex 8 $
        case Dwarf.cieVersion cie of
          4 -> Dwarf.fdeCiePointer fde
          3 -> 0
          _ -> off - Dwarf.fdeCiePointer fde + 4
      writeBuilder $ " pc="
      let addr = Dwarf.fdeStartAddress fde
      let ppPC a =
            case Dwarf.cieAddressSize cie of
              Just w -> ppHex (fromIntegral w) a
              Nothing ->
                let s = showHex a ""
                    n = length s
                 in replicate (8 - n) '0' ++ s
      writeBuilder $ fromString $ ppPC addr
      writeBuilder "..."
      writeBuilder $ fromString $ ppPC (addr + Dwarf.fdeAddressRange fde)
      writeBuilder "\n"
      writeBuilder "  Format:       "
      writeBuilder $ fromString $ ppEncoding $ Dwarf.fdeEncoding fde
      writeBuilder "\n"
      case Dwarf.fdeLsdaAddress fde (frameAddr f + off) of
        Nothing -> pure ()
        Just (a,ra) -> do
          writeLn $ "  LSDA Address: " <> ppHex 16 a
          case frameExcept f of
            Nothing -> pure ()
            Just s -> do
              let inRange = Elf.shdrAddr s <= ra
                         && (ra - Elf.shdrAddr s) < Elf.shdrSize s
              when (not inRange) $ reportError path "Invalid LSDA address."
      ppInsns path (frameData f) cie off (Dwarf.fdeSize fde) (Dwarf.fdeEncoding fde)
              (Dwarf.fdeInstructions fde)
      ppFDEs path f cie off'

ppBuffer :: BS.ByteString -> String
ppBuffer b = unwords $ fmap ppByte $ BS.unpack b

-- | This is hard-coded output to match the last CIE that dwarfdump emits
ppLastCIE :: WriteMonad m => Word64 -> m ()
ppLastCIE lastOff = writeLn $ ppHex 8 lastOff <> " ZERO terminator"

-- | Pretty print CIEs in file with
ppCIEs :: WriteMonad m
       => FilePath
       -> Dwarf.Endianess
       -> Frame
       -> Word64
       -> m ()
ppCIEs _ _ f off | BS.length (frameData f) <= fromIntegral off = pure ()
ppCIEs path end f off = do
  case Dwarf.getCIE (frameCtx f) end Dwarf.TargetSize64 (frameData f) off of
    Left (_, msg) ->
      reportError path $ "CIE " <> showHex off " parse failure: " <> msg
    Right (_, Nothing) -> do
      ppLastCIE off
    Right (off', Just cie)   -> do
      let enc | Dwarf.cieVersion cie >= 3 = "ffffffff"
              | otherwise                 = "00000000"
      writeLn $ ppHex 8 off ++ " " ++ ppHex 8 (Dwarf.cieSize cie) ++ " " ++ enc ++ " CIE"
--      writeLn $ show cie
      writeBuilder "  Format:                "
      writeBuilder $ fromString $ ppEncoding $ Dwarf.cieEncoding cie
      writeBuilder "\n"
      writeLn $ "  Version:               " ++ show (Dwarf.cieVersion cie)
      writeLn $ "  Augmentation:          " ++ show (Dwarf.cieAugmentation cie)
      case Dwarf.cieAddressSize cie of
        Just sz -> writeBuilder $ "  Address size:          " <> Bld.word8Dec sz <> "\n"
        Nothing -> pure ()
      case Dwarf.cieSegmentDescSize cie of
        Just sz -> writeBuilder $ "  Segment desc size:     " <> Bld.word8Dec sz <> "\n"
        Nothing -> pure ()

      writeLn $ "  Code alignment factor: " ++ show (Dwarf.cieCodeAlignmentFactor cie)
      writeLn $ "  Data alignment factor: " ++ show (Dwarf.cieDataAlignmentFactor cie)
      writeLn $ "  Return address column: " ++ show (Dwarf.cieReturnAddressRegister cie)
      case Dwarf.ciePersonality cie of
        Dwarf.NoCiePersonality -> pure ()
        Dwarf.IndirectCiePersonality _ a -> writeLn $ "  Personality Address: " ++ ppHex 16 a
        Dwarf.DirectCiePersonality   _ a -> writeLn $ "  Personality Address: " ++ ppHex 16 a
      unless (BS.null (Dwarf.cieAugmentationData cie)) $ do
        writeLn $ "  Augmentation data:     " ++ ppBuffer (Dwarf.cieAugmentationData cie)
      writeLn ""
      ppInsns path (frameData f) cie off (Dwarf.cieSize cie) (Dwarf.cieEncoding cie)
              (Dwarf.cieInitialInstructions cie)
      fdeErr <- ppFDEs path f  cie off'
      writeBuilder "\n"
      case fdeErr of
        Dwarf.FDEReachedEnd -> pure ()
        Dwarf.FDEParseError fdeOff msg -> do
          reportError path $ "FDE error " ++ showHex fdeOff ": " ++ msg
        Dwarf.FDECIE nextCIEOff -> do
          ppCIEs path end f nextCIEOff
        Dwarf.FDEEnd lastOff -> do
          ppLastCIE lastOff

withFrame ::
  WriteMonad m =>
  FilePath ->
  Elf.ElfHeaderInfo 64 ->
  Map.Map BS.ByteString [Elf.Shdr BS.ByteString Word64] ->
  BS.ByteString ->
  (Elf.ElfWordType 64 -> BS.ByteString -> [Elf.RelaEntry Elf.X86_64_RelocationType] -> m ()) ->
  m ()
withFrame path elfFile shdrMap s act = do
  case Map.findWithDefault [] s shdrMap of
    frameSection : rest -> do
      when (not (null rest)) $ do
        reportError path $ "Multiple " <> BSC.unpack s <> " sections."
      let dta = Elf.shdrData elfFile frameSection

      relaEntries <-
        case Map.findWithDefault [] (".rela" <> s) shdrMap of
          relaSec:r -> do
            when (not (null r)) $ do
              reportError path $ "Multiple .rela" <> BSC.unpack s <> " sections."
            let relaDta = Elf.shdrData elfFile frameSection
            case Elf.decodeRelaEntries (Elf.headerData (Elf.header elfFile)) relaDta of
              Left msg -> reportError path $ "Error decoding rela entries: " <> msg
              Right l -> pure l
          [] -> do
            pure []
      act (Elf.shdrAddr frameSection) dta relaEntries
    [] -> do
      pure ()

mkDwarfdumpOutput :: WriteMonad m => FilePath -> Elf.ElfHeaderInfo 64 -> m ()
mkDwarfdumpOutput path elfFile = do

  shdrMap <-
    case Elf.headerNamedShdrs elfFile of
      Left _ -> reportError path $ "Could not parse section header table."
      Right shdrs -> do
        pure $!
          Map.fromListWith (++) [ (Elf.shdrName s, [s]) | s <- V.toList shdrs ]

  mExceptTable <-
    case Map.findWithDefault [] ".gcc_except_table" shdrMap of
      s:r -> do
        when (not (null r)) $ do
          reportError path "Multiple .gcc_except_table sections."
        pure (Just s)
      [] ->
        pure Nothing

  writeBuilder $ fromString path
  writeBuilder ":\tfile format elf64-x86-64\n\n"
  writeBuilder ".debug_frame contents:\n\n"
  withFrame path elfFile shdrMap ".zdebug_frame" $ \faddr fdata frel -> do
    unless ("ZLIB" `BS.isPrefixOf` fdata) $ do
      reportError path $ "Expected compressed section to start with \"ZLIB\"."
    when (BS.length fdata < 12) $
      reportError path $ "Expected compressed section to contain uncompressed size."
    let uncompressedSize = Elf.bsWord64be (BS.drop 4 fdata)
    let uncompressedData = BSL.toStrict $ Zlib.decompress $ BSL.fromStrict $ BS.drop 12 fdata
    when (fromIntegral (BS.length uncompressedData) /= uncompressedSize) $ do
      reportError path "Uncompressed .zdebug_frame size is incorrect."
    when (not (null frel)) $ do
      reportError path "Relocations unsupported."
    let f = Frame { frameCtx = Dwarf.DebugFrame
                  , frameAddr = faddr
                  , frameData = uncompressedData
                  , frameExcept = mExceptTable
                  }
    ppCIEs path Dwarf.LittleEndian f 0
  withFrame path elfFile shdrMap ".debug_frame" $ \faddr fdata frel -> do
    when (not (null frel)) $ do
      reportError path "Relocations unsupported."
    let f = Frame { frameCtx = Dwarf.DebugFrame
                  , frameAddr = faddr
                  , frameData = fdata
                  , frameExcept = mExceptTable
                  }
    ppCIEs path Dwarf.LittleEndian f 0

  writeBuilder "\n.eh_frame contents:\n\n"
  withFrame path elfFile shdrMap ".eh_frame" $ \faddr fdata frel -> do
    when (not (null frel)) $ do
      reportError path "Relocations unsupported."
    let f = Frame { frameCtx = Dwarf.EhFrame
                  , frameAddr = faddr
                  , frameData = fdata
                  , frameExcept = mExceptTable
                  }
    ppCIEs path Dwarf.LittleEndian f 0

newtype Exporter a = Exporter (State Bld.Builder a)
  deriving (Functor, Applicative, Monad)

instance WriteMonad Exporter where
  writeBuilder msg = Exporter $ modify $ \l -> l <> msg
  writeLn msg = Exporter $ modify $ \l -> l <> Bld.string8 msg <> "\n"
  reportError path msg = error $ path <> ": " <> msg

runExporter :: Exporter () -> BSL.ByteString
runExporter (Exporter m) = Bld.toLazyByteString (execState m mempty)

-- | @compareElf dwarfDump path@ compares the output of the Haskell
-- ehframe parsing on output with the output of @dwarfDump --eh-frame
-- path@ and fails if they are different.
compareElf :: FilePath -> FilePath -> BS.ByteString -> IO ()
compareElf dwarfDump path bytes = do
  putStrLn $ "Checking " <> path
  case Elf.decodeElfHeaderInfo bytes of
    Left (_o, m) -> reportError path m
    Right (Elf.SomeElf elfHdr)
      | hdr <- Elf.header elfHdr
      , Elf.ELFCLASS64 <- Elf.headerClass hdr
      , Elf.EM_X86_64 <- Elf.headerMachine hdr
      , Elf.headerType hdr `elem` [Elf.ET_EXEC, Elf.ET_DYN] -> do

      let myDwarfDump = runExporter (mkDwarfdumpOutput path elfHdr)
      llvmDwarfDump <- fromString <$> P.readProcess dwarfDump  ["--eh-frame", path] ""

      if myDwarfDump == llvmDwarfDump then
        pure ()
       else do
        BSL.writeFile "lldd" llvmDwarfDump
        BSL.writeFile "mcdd" myDwarfDump
        reportError path "Output different: See mcdd and lldd"
    Right _ -> do
      -- For now we skip 32bit and non-x86 files.
      pure ()

-- | Runs the action on each file in a directory (recursively)
foreachFile :: (FilePath -> IO ()) -> FilePath -> IO ()
foreachFile act path = do
  -- Ignore sym links
  isLink <- pathIsSymbolicLink path
  if isLink then
    pure ()
   else do
    dexist <- doesDirectoryExist path
    if dexist then do
      mentries <- try $ listDirectory path
      case mentries of
        Left (e :: IOException) -> do
          pure ()
        Right entries -> do
          mapM_ (\f -> foreachFile act (path </> f)) entries
     else do
      fexist <- doesFileExist path
      when (fexist && not isLink) (act path)

-- | This reads an argument in the file.
compareArg :: FilePath -> FilePath -> IO ()
compareArg dwarfDump path = do
  fexist <- doesFileExist path

  if fexist then do
    mbytes <- try $ BS.readFile path
    case mbytes of
      Left (e :: IOException) -> do
        pure ()
      Right bytes -> do
        compareElf dwarfDump path bytes
   else do
    dexist <- doesDirectoryExist path
    if dexist then do
      let m fname = do
            mbytes <- try $ BS.readFile fname
            case mbytes of
              -- Ignore files we cannot read
              Left (_e :: IOException) -> do
                pure ()
              Right bytes -> do
                when (Elf.elfMagic `BS.isPrefixOf` bytes) $
                  compareElf dwarfDump fname bytes
      mentries <- try $ listDirectory path
      case mentries of
        Left (e :: IOException) -> do
          pure ()
        Right entries -> do
          mapM_ (\f -> foreachFile m (path </> f)) entries
     else do
      reportError path "File not found"

main :: IO ()
main = do
  paths <- getArgs
  when (null paths) $ do
    hPutStrLn stderr $ "Please specify at least one file or directory for comparing."
    exitFailure
  mapM_ (compareArg "llvm-dwarfdump") paths
  putStrLn "Exact output match"
