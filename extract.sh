#!/usr/bin/env bash

set -e

# may require GNU sed
COQC="coqc $(sed '/^[[:space:]]*$/q' _CoqProject)"

$COQC -Q src "" ${1}


