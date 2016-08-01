#!/usr/bin/env bash

COMP="./OeufDriver.native"

TESTS="
  fib.oeuf
  add.oeuf
  echo_initial_state.oeuf
  echo_handleInput.oeuf
  echo_handleMsg.oeuf
  "

# ANSI color codes
BK=$'\033[1;30m' # black
RD=$'\033[1;31m' # red
GR=$'\033[1;32m' # green
YL=$'\033[1;33m' # yellow
BL=$'\033[1;34m' # blue
MG=$'\033[1;35m' # magenta
CY=$'\033[1;36m' # cyan
WT=$'\033[1;37m' # white
NC=$'\033[0m'    # no color

PASS="PASS"
FAIL="FAIL"
if [ -t 1 ]; then
  PASS="${GR}PASS${NC}"
  FAIL="${RD}FAIL${NC}"
fi

if ! [ -f "$COMP" ]; then
  cat <<EOF
ERROR: $COMP does not exist.

Please run 'make' to build $COMP.
EOF
  exit 1
fi

for t in $TESTS; do
  printf "%-25s" "$t"
  out="$(basename "$t" .oeuf).o"
  "$COMP" -c "$t"
  if [ -f "$out" ]; then
    echo "$PASS"
    rm "$out"
  else
    echo "$FAIL"
  fi
done
