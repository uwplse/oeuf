#!/bin/bash

ocamlc `cat compcert_includes` -c src/OeufDriver.ml
ocamlopt `cat compcert_includes` -c src/OeufDriver.ml

if [ -z "$MENHIR_LIBDIR" ]; then
    MENHIR_LIBDIR=/usr/lib/ocaml/menhirLib
fi

ocamlopt -o ccomp \
    str.cmxa unix.cmxa \
    -I "${MENHIR_LIBDIR}" menhirLib.cmx \
    `cat compcert_includes` \
    `compcert/tools/modorder compcert/.depend.extr driver/Driver.cmx | \
        sed -e 's: driver/Driver.cmx.*::' -e 's:\(^\| \):&compcert/:g'` \
    src/OeufDriver.cmx
