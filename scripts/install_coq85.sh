#!/bin/bash

set -evuo pipefail
IFS=$'\n\t'

#if we don't already have a coqc command, download coq and install from source
if ! [ -x "$(command -v coqc)" ]; then

    wget -P $HOME/.cache/coq "https://coq.inria.fr/distrib/V8.5pl3/files/coq-8.5pl3.tar.gz"
    pushd $HOME/.cache/coq
    tar -xvf coq-8.5pl3.tar.gz
    pushd coq-8.5pl3
    ./configure -bindir ~/.cache/bin -libdir ~/.cache/lib -configdir /dev/null -datadir /dev/null -mandir /dev/null -docdir /dev/null -emacslib /dev/null -coqdocdir /dev/null
    make
    make install
    popd
    popd

fi
