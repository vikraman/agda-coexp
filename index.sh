#!/usr/bin/env bash

set -eu
set -o pipefail

for file in $( find -H Coexp -type f -name '*.agda' | sort ); do
    i=$( echo ${file} | sed 's/Coexp\/\(.*\)\.agda/Coexp\/\1/' | sed 's/\//\./g' )
    echo "import ${i}" >> index.agda
done
