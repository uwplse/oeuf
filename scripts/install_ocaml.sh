#!/bin/bash

set -evuo pipefail
IFS=$'\n\t'


if ! [ -x "$(command -v ocamlc)" ]; then

    opam init -y --comp=4.02.3
    opam update
    opam install camlp5
fi
