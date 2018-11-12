#!/bin/bash
set -e

# make sure graphmod and dot are in the PATH
if ! type -p graphmod || ! type -p dot; then
    echo "Error: cannot find 'graphmod' and/or 'dot' in PATH" 1>&2
    exit 1
fi

include="-i base/src -i x86/src"
files="$(find base/src -name '*.hs') $(find x86/src -name '*.hs')"

echo "Writing graphmod file to macaw.svg"
graphmod $include --no-cluster $files -q | dot -Tsvg > macaw.svg

echo "Writing graphmod file to macaw_cluster.svg"
graphmod $include -p $files -q | dot -Tsvg > macaw_cluster.svg
