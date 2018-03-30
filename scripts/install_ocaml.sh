#!/bin/bash

set -evuo pipefail
IFS=$'\n\t'


#only run if coq not around
if ! [ -x "$(command -v coqc)" ]; then

    opam init -y --comp=4.02.3
    opam update
    opam install camlp5
    opam install menhir
    eval $(opam config env)
    
fi
