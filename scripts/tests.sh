#!/bin/bash

./submodules/dismantle/scripts/minify-asl.sh
cd ./submodules/asl-translator/
make genarm
cd ../../

cabal v2-build --only-dependencies macaw-asl
