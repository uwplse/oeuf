#!/bin/bash
set -e

#make -f Makefile.extr depend
#make -f Makefile.extr extraction/OeufDriver.cmx
ocamlopt -o ccomp str.cmxa unix.cmxa \
    -I /usr/lib/ocaml/menhirLib menhirLib.cmx  \
    -I extraction \
    `compcert/tools/modorder .depend.extr extraction/OeufDriver.cmx`
