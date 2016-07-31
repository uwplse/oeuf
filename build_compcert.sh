#!/usr/bin/env bash

set -e

if [ "$(uname)" = "Darwin" ]; then
  NBUILDPROCS="$(expr $(gnproc) - 1)"
  CCOMPCONFIG="ia32-macosx"
else
  NBUILDPROCS="$(expr $(nproc) - 1)"
  CCOMPCONFIG="ia32-linux"
fi

pushd compcert
./configure "$CCOMPCONFIG"
make -j"$NBUILDPROCS" proof
make driver/Version.ml
make -f Makefile.extr cparser/pre_parser_messages.ml
popd
