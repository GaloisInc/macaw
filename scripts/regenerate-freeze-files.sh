#!/usr/bin/env bash
#
# Regenerate the freeze files for CI. This should be run from the root of the repository

cabal freeze -w ghc-8.8.4
mv cabal.project.freeze cabal.project.freeze.ghc-8.8.4

cabal freeze -w ghc-8.10.7
mv cabal.project.freeze cabal.project.freeze.ghc-8.10.7

cabal freeze -w ghc-9.0.2
mv cabal.project.freeze cabal.project.freeze.ghc-9.0.2
