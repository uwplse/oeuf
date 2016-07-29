#!/bin/bash
set -e

ocamlbuild \
    -use-menhir -pkg menhirLib \
    -yaccflag --table \
    -lib str \
    -lib unix \
    -I src \
    -I extraction \
    -I compcert/driver \
    -I compcert/cfrontend \
    -I compcert/cparser \
    -I compcert/ia32 \
    -I compcert/lib \
    -I compcert/common \
    -I compcert/debug \
    -I compcert/backend \
    OeufDriver.native

rm -f OeufDriver.native
cp _build/src/OeufDriver.native .
