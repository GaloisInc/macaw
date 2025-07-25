{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Macaw.BinaryLoader.Raw (RawBinLoadException (..)) where

import Control.Monad.Catch (MonadThrow (throwM))
import qualified Data.ByteString as BS
import Data.Macaw.BinaryLoader (BinaryLoader (..))
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG.Core as MR
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.LoadCommon as LC
import qualified Data.Macaw.Memory.Permissions as MM
import Data.Macaw.Types (KnownNat, knownNat)
import qualified Data.Map as Map
import qualified GHC.Exception as X

segFromRawBS :: (MM.MemWidth w, Monad m) => BS.ByteString -> Integer -> m (MM.MemSegment w)
segFromRawBS bs loadBase =
    let wordBase = fromIntegral loadBase
        sz = fromIntegral (BS.length bs)
        baseRegionIndex = 0
        segmentOffset = 0
     in MM.memSegment Map.empty baseRegionIndex segmentOffset Nothing wordBase MM.execute bs sz

memFromRawBS :: (MM.MemWidth w, MonadThrow m, KnownNat w) => BS.ByteString -> Integer -> m (MM.Memory w)
memFromRawBS bs base = do
    let w = MM.addrWidthRepr knownNat
    let emp = MM.emptyMemory w
    seg <- segFromRawBS bs base
    case MM.insertMemSegment seg emp of
        -- Should be impossible as we insert a single segment
        Left (MM.OverlapSegment _ _) -> throwM OverlappingSegments
        Right mem -> pure mem

{- | Loads a "raw" binary at a fixed offset. Loading a binary in this way assumes that
it is a position-dependent, statically linked binary. The information parsed from such a
binary is consequently limited. Entrypoints and symbols do not exist, and the memory will simply
represent the binary at a fixed base address in a single segment.
-}
instance (MM.MemWidth (MR.ArchAddrWidth arch), KnownNat (MR.ArchAddrWidth arch)) => (BinaryLoader arch MBL.RawBin) where
    type ArchBinaryData arch MBL.RawBin = ()
    type BinaryFormatData arch MBL.RawBin = ()
    type Diagnostic arch MBL.RawBin = ()
    loadBinary lc bin = do
        let off = LC.loadRegionBaseOffset lc
        mem <- memFromRawBS (MBL.rawContents bin) off
        pure
            MBL.LoadedBinary
                { MBL.memoryImage = mem
                , MBL.memoryEndianness = (MBL.rawEndianess bin)
                , MBL.archBinaryData = ()
                , MBL.binaryFormatData = ()
                , MBL.loadDiagnostics = []
                , MBL.binaryRepr = MBL.RawBinary
                , MBL.originalBinary = bin
                , MBL.loadOptions = lc
                }

    entryPoints _ = pure []
    symbolFor _ _ = throwM MissingSymbol

-- | Exceptions for loading a raw binary
data RawBinLoadException
    = -- | Looked for the symbol at an address where no symbol exists
      -- for a raw binary no addresses should have symbols
      MissingSymbol
    | -- | An error building out segments during loading
      OverlappingSegments

deriving instance Show RawBinLoadException

instance X.Exception RawBinLoadException
