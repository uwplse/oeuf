#!/usr/bin/env bash

set -e

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DRIVER="${ROOT}/OeufDriver.native"
DRIVER_OPTS=""
SHIM="${ROOT}/shims/${1}_shim.c"

if ! [ -f "$DRIVER" ]; then
  echo "could not find Oeuf driver, please build first"
  exit 1
fi

if ! [ -f "$SHIM" ]; then
  echo "sorry, could not find shim for $1"
  exit 1
fi

cp "$SHIM" shim.c
$DRIVER $DRIVER_OPTS "${1}.oeuf" shim.c || { echo "Driver failed during compilation." >&2; exit 1; }
