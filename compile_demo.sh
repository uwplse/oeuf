#!/usr/bin/env bash

set -e


#coq compiler with dependencies
COQC="coqc $(sed '/^[[:space:]]*$/q' _CoqProject)"

#compile demo.v to get .oeuf file
$COQC -Q src "" "test/List_Demo.v" >/dev/null 2>&1 || { echo "coqc failed on List_Demo.v"; exit 1; }

#use Oeuf driver to get compile .oeuf file
./occ.sh list_demo >/dev/null 2>&1 || { echo "occ.sh failed on list_demo"; exit 1; }

