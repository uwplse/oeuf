#!/usr/bin/env bash

set -e

if [ "$(uname)" = "Darwin" ]; then
  NBUILDPROCS="$(expr $(gnproc) - 1)"
else
  NBUILDPROCS="$(expr $(nproc) - 1)"
fi

bash build_compcert.sh
./configure
make -j"$NBUILDPROCS" proof
make driver
