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
make -j"$NBUILDPROCS" # not just proof, need compcert.ini
make driver/Version.ml
make -f Makefile.extr cparser/pre_parser_messages.ml
popd
ln -sf compcert/compcert.ini compcert.ini

./configure
make -j"$NBUILDPROCS"

# absurd: build.sh once so ocamlbuild tells us what
# files to sanitize, sanitize them, clear out ocamlbuild
# dir, then try to build again
#
# this appears to work every other attempt (?!)
bash build.sh || \
  _build/sanitize.sh && rm -r _build/ && bash build.sh
