{-|
compare-dwarfdump generate dwarfdump-output on specific parts of binary,
and reports inconsistencies.

It currently only supports .eh_frame and .debug_frame sections.
-}
{-# LANGUAGE DataKinds #-}
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
import qualified Data.ByteString.Builder as Bld
import qualified Data.ByteString.Lazy as BSL
import           Data.Char
import qualified Data.ElfEdit as Elf
import qualified Data.ElfEdit.ByteString as Elf
import           Data.String
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

-- | Print a word64 valuew with exactly 8 digits of output.
ppHex :: Word64 -> String
ppHex x =
  let s = showHex x ""
      n = length s
   in replicate (8 - n) '0' ++ drop (n-8) s

-- | Print a word64 valuew with exactly 8 digits of output.
ppAddr :: Word64 -> String
ppAddr x =
  let s = showHex x ""
      n = length s
   in replicate (16 - n) '0' ++ drop (n-16) s


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
                                   }
  case Dwarf.parseCallFrameInstructions end tgtSize insnBuf of
    Left (prev, insnOff, msg) -> do
      let ctxBytes = BS.take (fromIntegral ctxSize) $ BS.drop (fromIntegral off) ehFrameData
      reportError path
        $ ppHex (fromIntegral off) <> " instruction parse failure.\n"
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
                   , frameData :: !BS.ByteString
                     -- ^ Byres in frame
                   , frameAddr :: !Word64
                     -- ^ Address frame is loaded at.
                   , frameExcept :: Maybe (Elf.ElfSection Word64)
                     -- ^ Section for .gcc_except_table if defined.
                     --
                     -- Used so we validate that we understand the
                     -- LSDA address.
                   }

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
      let addr = Dwarf.fdeStartAddress fde
      writeBuilder "\n"
      writeBuilder $ fromString $ ppHex off
      writeBuilder " "
      writeBuilder $ fromString $ ppHex (Dwarf.fdeSize fde)
      writeBuilder " "
      writeBuilder $ fromString $ ppHex (Dwarf.fdeCiePointer fde)
      writeBuilder " FDE cie="
      writeBuilder $ fromString $ ppHex (Dwarf.fdeCiePointer fde)
      writeBuilder $ " pc="
      writeBuilder $ fromString $ ppHex addr
      writeBuilder "..."
      writeBuilder $ fromString $ ppHex (addr + Dwarf.fdeAddressRange fde)
      writeBuilder "\n"
      case Dwarf.fdeLsdaAddress fde (frameAddr f + off) of
        Nothing -> pure ()
        Just (a,ra) -> do
          writeLn $ "  LSDA Address: " <> ppAddr a
          case frameExcept f of
            Nothing -> pure ()
            Just s -> do
              let inRange = Elf.elfSectionAddr s <= ra
                         && (ra - Elf.elfSectionAddr s) < Elf.elfSectionSize s
              when (not inRange) $ reportError path "Invvalid LSDA address."
      ppInsns path (frameData f) cie off (Dwarf.fdeSize fde) (Dwarf.fdeEncoding fde)
              (Dwarf.fdeInstructions fde)
      ppFDEs path f cie off'

ppBuffer :: BS.ByteString -> String
ppBuffer b = unwords $ fmap ppByte $ BS.unpack b

-- | This is hard-coded output to match the last CIE that dwarfdump emits
ppLastCIE :: WriteMonad m => Word64 -> m ()
ppLastCIE lastOff = do
  writeLn $ ppHex lastOff <> " 00000000 ffffffff CIE"
  writeLn "  Version:               0"
  writeLn "  Augmentation:          \"\""
  writeLn "  Code alignment factor: 0"
  writeLn "  Data alignment factor: 0"
  writeLn "  Return address column: 0"
  writeLn ""
  writeLn ""

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
      writeLn $ ppHex off ++ " " ++ ppHex (Dwarf.cieSize cie) ++ " ffffffff CIE"
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
        Dwarf.IndirectCiePersonality _ a -> writeLn $ "  Personality Address: " ++ ppAddr a
        Dwarf.DirectCiePersonality   _ a -> writeLn $ "  Personality Address: " ++ ppAddr a
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

mkDwarfdumpOutput :: WriteMonad m => FilePath -> Elf.Elf 64 -> m ()
mkDwarfdumpOutput path elfFile = do
  let mExceptTable =
        case Elf.findSectionByName ".gcc_except_table" elfFile of
          [s] -> Just s
          _ -> Nothing

  writeBuilder $ fromString path
  writeBuilder ":\tfile format ELF64-x86-64\n\n"
  writeBuilder ".debug_frame contents:\n\n"
  case Elf.findSectionByName ".zdebug_frame" elfFile of
    [frameSection] -> do
      let compressedData = Elf.elfSectionData frameSection
      unless ("ZLIB" `BS.isPrefixOf` compressedData) $ do
        reportError path $ "Expected compressed section to start with \"ZLIB\"."
      when (BS.length compressedData < 12) $
        reportError path $ "Expected compressed section to contain uncompressed size."
      let uncompressedSize = Elf.bsWord64be (BS.drop 4 compressedData)
      let frameData = BSL.toStrict $ Zlib.decompress $ BSL.fromStrict $ BS.drop 12 compressedData
      when (fromIntegral (BS.length frameData) /= uncompressedSize) $ do
        reportError path "Uncompressed .zdebug_frame size is incorrect."
      let f = Frame { frameCtx = Dwarf.DebugFrame
                    , frameData = frameData
                    , frameAddr = Elf.elfSectionAddr frameSection
                    , frameExcept = mExceptTable
                    }
      ppCIEs path Dwarf.LittleEndian f 0
    _ -> pure ()
  case Elf.findSectionByName ".debug_frame" elfFile of
    [frameSection] -> do
      let frameData = Elf.elfSectionData frameSection
      let f = Frame { frameCtx = Dwarf.DebugFrame
                    , frameData = frameData
                    , frameAddr = Elf.elfSectionAddr frameSection
                    , frameExcept = mExceptTable
                    }
      ppCIEs path Dwarf.LittleEndian f 0
    _ -> pure ()

  writeBuilder "\n.eh_frame contents:\n\n"
  case Elf.findSectionByName ".eh_frame" elfFile of
    [frameSection] -> do
      let f = Frame { frameCtx = Dwarf.EhFrame
                    , frameData = Elf.elfSectionData frameSection
                    , frameAddr = Elf.elfSectionAddr frameSection
                    , frameExcept = mExceptTable
                    }
      ppCIEs path Dwarf.LittleEndian f 0
    _ -> pure ()

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
  case Elf.parseElfHeaderInfo bytes of
    Left (_o, m) -> reportError path m
    Right (Elf.Elf64 elfHdr) | Elf.EM_X86_64 <- Elf.headerMachine (Elf.header elfHdr)  -> do
      let (errs, elfFile) = Elf.getElf elfHdr
      forM_ errs $ \e -> hPutStrLn stderr (show e)
      let myDwarfDump = runExporter (mkDwarfdumpOutput path elfFile)
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
      mapM_ (\f -> foreachFile act (path </> f)) =<< listDirectory path
     else do
      fexist <- doesFileExist path
      when (fexist && not isLink) (act path)

-- | This reads an argument in the file.
compareArg :: FilePath -> FilePath -> IO ()
compareArg dwarfDump path = do
  fexist <- doesFileExist path

  if fexist then
    compareElf dwarfDump path =<< BS.readFile path
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
      mapM_ (\f -> foreachFile m (path </> f)) =<< listDirectory path
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
