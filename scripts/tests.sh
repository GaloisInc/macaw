#!/bin/bash

./deps/dismantle/scripts/minify-asl.sh
cd ./deps/asl-translator/
make genarm
cd ../../

cabal v2-build --only-dependencies macaw-asl
