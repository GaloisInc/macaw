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

module Data.Macaw.BinaryLoader.Raw () where

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
     in MM.memSegment Map.empty 0 0 Nothing wordBase MM.execute bs sz

memFromRawBS :: forall w m. (MM.MemWidth w, MonadThrow m, KnownNat w) => BS.ByteString -> Integer -> m (MM.Memory w)
memFromRawBS bs base = do
    let x = MM.addrWidthRepr knownNat
    let emp = MM.emptyMemory x
    seg <- segFromRawBS bs base
    case MM.insertMemSegment seg emp of
        Left _ -> throwM OverlappingSegments
        Right mem -> pure mem

{- | Loads a "raw" binary at a fixed offset. Loading a binary in this way assumes that
it is a position-dependent, statically linked binary. The information parsed from such a
binary is consequently limited. Entrypoints and symbols do not exist, and the memory will simply
represent the binary at a fixed base address in a single segment.
-}
instance ((MM.MemWidth (MR.ArchAddrWidth arch)), KnownNat (MR.ArchAddrWidth arch)) => (BinaryLoader arch MBL.RawBin) where
    type ArchBinaryData arch MBL.RawBin = ()
    type BinaryFormatData arch MBL.RawBin = ()
    type Diagnostic arch MBL.RawBin = ()
    loadBinary lc bin = do
        let off = LC.loadRegionBaseOffset lc
        let (MBL.RawBin bs end) = bin
        mem <- memFromRawBS bs off
        pure
            MBL.LoadedBinary
                { MBL.memoryImage = mem
                , MBL.memoryEndianness = end
                , MBL.archBinaryData = ()
                , MBL.binaryFormatData = ()
                , MBL.loadDiagnostics = []
                , MBL.binaryRepr = MBL.RawBinary
                , MBL.originalBinary = bin
                , MBL.loadOptions = lc
                }

    entryPoints _ = pure []
    symbolFor _ _ = throwM MissingSymbol

data RawBinLoadException
    = MissingSymbol
    | OverlappingSegments

deriving instance Show RawBinLoadException

instance X.Exception RawBinLoadException
