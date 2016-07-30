#!/usr/bin/env bash

set -e
set -x

if [ "$(uname)" = "Darwin" ]; then
  NBUILDPROCS="$(expr $(gnproc) - 1)"
  CCOMPCONFIG="ia32-macosx"
else
  NBUILDPROCS="$(expr $(nproc) - 1)"
  CCOMPCONFIG="ia32-linux"
fi

pushd compcert
./configure "$CCOMPCONFIG"
if [ -f "compcert.ini" ]; then
  make -j"$NBUILDPROCS" proof
else
  make -j"$NBUILDPROCS"
fi
make driver/Version.ml
make -f Makefile.extr cparser/pre_parser_messages.ml
popd
ln -sf compcert/compcert.ini compcert.ini

./configure
make -j"$NBUILDPROCS"

# TODO fix this absurd monstrosity
rm -rf _build/
bash build.sh || true
_build/sanitize.sh
bash build.sh
