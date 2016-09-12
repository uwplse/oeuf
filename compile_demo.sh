#!/usr/bin/env bash

set -e


#coq compiler with dependencies
COQC="coqc $(sed '/^[[:space:]]*$/q' _CoqProject)"

#compile demo.v to get .oeuf file
$COQC -Q src "" "test/demo.v" >/dev/null 2>&1 || { echo "coqc failed on $f"; exit 1; }

#use Oeuf driver to get compile .oeuf file
./occ.sh demo >/dev/null 2>&1 || { echo "occ.sh failed on demo"; exit 1; }

