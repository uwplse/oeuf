#!/usr/bin/env bash

set -e

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DRIVER="${ROOT}/OeufDriver.native"
TEMPLATE="${ROOT}/shim_templates/${1}_shim.c"

function target_sym {
  src="${1}.oeuf"
  asm="${1}.s"
  ./OeufDriver.native -S "$src"
  cat "$asm" \
    | sed -n -e 's/^_\(_\$.*\):/\1/p' \
    | tail -n 1
  rm "$asm"
}

if ! [ -f "$DRIVER" ]; then
  echo "could not find Oeuf driver, please build first"
  exit 1
fi

if ! [ -f "$TEMPLATE" ]; then
  echo "sorry, could not find shim template for $1"
  exit 1
fi

sed "s/TARGET_SYM/$(target_sym "$1")/g" "$TEMPLATE" > shim.c
./OeufDriver.native "${1}.oeuf" shim.c
