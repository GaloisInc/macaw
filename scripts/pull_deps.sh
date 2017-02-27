#!/bin/bash

set -e

clone ()
{
    local depname=$1
    local url=$2
    if [ -d deps/$depname ]; then
        pushd deps/$depname > /dev/null
        git pull
        popd > /dev/null
    else
        pushd deps > /dev/null
        git clone $url $depname
        popd > /dev/null
    fi
}

mkdir -p deps

clone elf-edit            git@github.com:GaloisInc/elf-edit.git
clone galois-dwarf        git@github.com:GaloisInc/dwarf.git
clone flexdis86           git@github.com:GaloisInc/flexdis86.git
clone parameterized-utils git@github.com:GaloisInc/parameterized-utils.git
