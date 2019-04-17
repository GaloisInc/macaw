{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

import           Control.Monad.ST ( stToIO )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Map as Map
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import qualified Lang.Crucible.CFG.Core as CC
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified What4.FunctionName as WFN
import qualified What4.ProgramLoc as WPL

translate :: forall arch ids
           . (MS.ArchInfo arch, MC.MemWidth (MC.ArchAddrWidth arch))
          => MD.DiscoveryFunInfo arch ids
          -> IO ()
translate dfi =
  case MS.archVals (Proxy @arch) of
    Nothing -> putStrLn "Architecture does not support symbolic reasoning"
    Just MS.ArchVals { MS.archFunctions = archFns } -> do
      hdlAlloc <- CFH.newHandleAllocator
      let nameText = TE.decodeUtf8With TEE.lenientDecode (MD.discoveredFunName dfi)
      let name = WFN.functionNameFromText nameText
      let posFn addr = WPL.BinaryPos nameText (maybe 0 fromIntegral (MC.segoffAsAbsoluteAddr addr))
      cfg <- stToIO $ MS.mkFunCFG archFns hdlAlloc Map.empty name posFn dfi
      useCFG cfg

useCFG :: CC.SomeCFG (MS.MacawExt arch) (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch) -> IO ()
useCFG _ = return ()

main :: IO ()
main = return ()
