-- | Structured tracing for macaw code discovery
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Macaw.Discovery.Trace 
  ( TraceData(..)
  , Trace
  , showSimpleTrace
  , mkTrace
  , ppTraceData
  , ppTrace
  ) where

import           GHC.Stack

import qualified Prettyprinter as PP
import           Prettyprinter ( (<+>) )
import           Data.Macaw.AbsDomain.AbsState as AbsState
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory

data TraceData arch = 
      ClassifierMonadFail !String
    | Log !String
    | forall ids tp. MacawValue !String !(Value arch ids tp)
    | forall w tp. MemWidth w => MacawAbsValue !String !(AbsValue w tp)
    | NamedClassifier !String
    | NestedTraceData !(TraceData arch) ![Trace arch]

ppTraceData :: ArchConstraints arch 
            => (Trace arch -> PP.Doc a) 
            -> TraceData arch
            -> PP.Doc a
ppTraceData printTrace traceData = case traceData of
    ClassifierMonadFail msg -> "fail:" <> PP.indent 1 (PP.viaShow msg)
    Log msg -> "fail:" <> PP.indent 1 (PP.viaShow msg)
    MacawValue msg v -> "Macaw Value:" <+> case null msg of
      True -> PP.pretty v
      False -> PP.viaShow msg <> PP.indent 1 (PP.pretty v)
    MacawAbsValue msg v -> "Macaw Abstract Value:" <+> case null msg of
      True -> PP.pretty v
      False -> PP.viaShow msg <> PP.indent 1 (PP.pretty v)
    NamedClassifier nm  -> "Classifier Failure:" <+> PP.viaShow nm
    -- as a special case: we print out all of the bindings for a macaw 'Value'
    -- if it's being nested
    -- this is so that we can establish the binding context for an expression once
    -- and just print the identifier for each individual expression when
    -- tracing a 'MacawValue'
    NestedTraceData (MacawValue msg v) subTraces -> 
      PP.viaShow msg <> PP.line 
      <> ppValueAssignments v 
      <> PP.indent 1 (PP.vsep (reverse $ map printTrace subTraces))
    NestedTraceData traceData' subTraces -> 
      ppTraceData printTrace traceData' 
      -- NB: the head of the trace is the most recent tracing data, so we
      -- reverse on display to give the natural ordering
      <> PP.indent 1 (PP.vsep (reverse $ map printTrace subTraces))


ppTrace :: ArchConstraints arch 
        => (TraceData arch -> PP.Doc a)
        -> (CallStack -> Maybe (PP.Doc a))
        -> Trace arch
        -> PP.Doc a
ppTrace printTraceData printCallStack tr = 
  case printCallStack (trCallStack tr) of
    Nothing -> printTraceData (trData tr)
    Just ppstk -> PP.vsep [ppstk, printTraceData (trData tr)]

instance ArchConstraints arch => PP.Pretty (TraceData arch) where
  pretty td = ppTraceData PP.pretty td

instance ArchConstraints arch => PP.Pretty (Trace arch) where
    pretty tr = ppTrace PP.pretty (\stk -> Just (PP.viaShow stk)) tr

data Trace arch = Trace
  { trCallStack :: CallStack
  , trData :: TraceData arch
  }

showSimpleTrace :: ArchConstraints arch => Trace arch -> String
showSimpleTrace tr = show (PP.pretty (trData tr))

mkTrace :: TraceData arch -> Trace arch
mkTrace d = Trace callStack d
