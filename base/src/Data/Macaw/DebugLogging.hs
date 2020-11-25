{-|
Copyright        : (c) Galois, Inc 2015
Maintainer       : Simon Winwood <sjw@galois.com>

Provides utilities for logging debug messages to stderr.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ImplicitParams #-}
module Data.Macaw.DebugLogging
       ( DebugClass(..)
       , setDebugKeys
       , getDebugKeys
       , allDebugKeys
       , debugKeyDescription
       , debugKeyName
       , parseDebugKey
       , unsetDebugKeys
       -- , debugKeys
       , debug
       , debug'
       , debugM
       , debugM'
       ) where

import Data.IORef
import Data.List (find, (\\))
import Debug.Trace
import Prettyprinter
import Prettyprinter.Render.String
import System.IO.Unsafe -- For debugKeys
#if MIN_VERSION_base(4,9,0)
import GHC.Stack
#else
import GHC.SrcLoc
import GHC.Stack
#endif

{-# NOINLINE debugKeys #-}
debugKeys :: IORef [DebugClass]
debugKeys = unsafePerformIO $ newIORef [DUrgent]

setDebugKeys :: [DebugClass] -> IO ()
setDebugKeys keys = writeIORef debugKeys keys

unsetDebugKeys :: [DebugClass] -> IO ()
unsetDebugKeys keys = do
  modifyIORef debugKeys (\\ keys)

getDebugKeys :: [DebugClass]
getDebugKeys = unsafePerformIO $ readIORef debugKeys

allDebugKeys :: [DebugClass]
allDebugKeys = [toEnum 0 .. ]

-- Basically a tag we can use to turn on/off debug messages (only at
-- compile time though).
data DebugClass = DUrgent | DAbsInt | DCFG | DFunRecover | DFunctionArgs | DRegisterUse
                deriving (Eq, Ord, Enum, Show)

supportedKeys :: [(String, DebugClass, String)]
supportedKeys = [ ("urgent", DUrgent, "High priority warnings")
                , ("absint", DAbsInt, "Abstract interpretation phase")
                , ("cfg", DCFG, "CFG discovery phase")
                , ("recover", DFunRecover, "Function recovery phase")
                , ("reguse", DRegisterUse, "Register use")
                , ("funargs", DFunctionArgs, "Function argument discovery phase") ]

debugKeyDescription :: DebugClass -> String
debugKeyDescription k =
  case find (\(_, k', _) -> k == k') supportedKeys of
    Nothing -> error "Missing debug key"
    Just (_, _, descr) -> descr

debugKeyName :: DebugClass -> String
debugKeyName k =
  case find (\(_, k', _) -> k == k') supportedKeys of
    Nothing -> error "Missing debug key"
    Just (n, _, _) -> n

parseDebugKey :: String -> Maybe DebugClass
parseDebugKey n =
  (\(_, k, _) -> k) <$> find (\(n', _, _) -> n' == n) supportedKeys

{-# INLINE debug #-}
debug :: (?loc :: CallStack) => DebugClass -> String -> a -> a
debug cl msg x
  | cl `elem` getDebugKeys =
      -- let doesn't work here, it seems to break the magic that is ?loc
      trace (srcLocFile (snd (last (getCallStack ?loc))) ++ ":"
             ++ show (srcLocStartLine (snd (last (getCallStack ?loc)))) ++ ": ["
             ++ debugKeyName cl ++ "] "
             ++ msg) x
  | otherwise = x
  where
    -- fn = show (getCallStack ?loc)

debug' :: DebugClass -> Doc ann -> a -> a
debug' cl msg x = debug cl (renderString (layoutPretty opts msg)) x
  where opts = LayoutOptions (AvailablePerLine 100 0.8)

{-# INLINE debugM #-}
debugM :: (?loc :: CallStack, Monad m) => DebugClass -> String -> m ()
debugM cl msg
  | cl `elem` getDebugKeys =
      -- let doesn't work here, it seems to break the magic that is ?loc
      traceM (srcLocFile (snd (last (getCallStack ?loc))) ++ ":"
              ++ show (srcLocStartLine (snd (last (getCallStack ?loc)))) ++ ": ["
              ++ debugKeyName cl ++ "] "
              ++ msg)
  | otherwise = return ()

debugM' :: Monad m => DebugClass -> Doc ann -> m ()
debugM' cl msg = debugM cl (renderString (layoutPretty opts msg))
  where opts = LayoutOptions (AvailablePerLine 100 0.8)
