#!/bin/bash

set -evuo pipefail
IFS=$'\n\t'


if [ ! -d StructTact ]; then
    git clone https://github.com/uwplse/StructTact.git
fi

pushd StructTact
git pull
./configure
make -j2
popd
