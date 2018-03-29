#!/bin/bash

set -evuo pipefail
IFS=$'\n\t'

#if we don't already have a coqc command, download coq and install from source
if ! [ -x "$(command -v coqc)" ]; then

    wget -P $HOME/.cache/coq "https://coq.inria.fr/distrib/V8.5pl3/files/coq-8.5pl3.tar.gz"
    pushd $HOME/.cache/coq
    tar -xvf coq-8.5pl3.tar.gz
    pushd coq-8.5pl3
    ./configure
    make
    
    popd
    popd
fi
