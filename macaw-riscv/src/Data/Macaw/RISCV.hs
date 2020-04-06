{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.RISCV (
  -- * Macaw configurations
  riscv_info,
  -- * Type-level tags
  -- * PPC Types
  ) where

import qualified Data.Macaw.Architecture.Info as MI
import qualified GRIFT.Types as GT

riscv_info :: GT.RVRepr rv -> MI.ArchitectureInfo rv
riscv_info _ = undefined
