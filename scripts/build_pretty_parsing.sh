#!/bin/bash

set -evuo pipefail
IFS=$'\n\t'

pushd $HOME

if [ ! -d PrettyParsing ]; then
    git clone https://github.com/wilcoxjay/PrettyParsing.git
fi

pushd PrettyParsing
git pull
./configure
make
popd
popd

