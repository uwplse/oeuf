#!/usr/bin/env bash

COMP="./OeufDriver.native"

TESTS="
  id_nat
  long_id
  fib
  add
  echo_initial_state
  echo_handleInput
  echo_handleMsg
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

# only output color for ttys
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

echo ">> Object files produced:"
for t in $TESTS; do
  printf "%-25s" "$t"
  out="${t}.o"
  "$COMP" -c "${t}.oeuf"
  if [ -f "$out" ]; then
    echo "$PASS"
    rm "$out"
  else
    echo "$FAIL"
  fi
done
echo

echo ">> Compiles with shim:"
for t in $TESTS; do
  printf "%-25s" "$t"
  if ./occ.sh "$t" > /dev/null 2>&1 ; then
    echo "$PASS"
    rm a.out shim.o "${t}.o"
  else
    echo "$FAIL"
  fi
done
echo

echo ">> Shim output (if compiles):"
for t in $TESTS; do
  if ./occ.sh "$t" > /dev/null 2>&1 ; then
    echo "$t"
    ./a.out
    rm a.out shim.o "${t}.o"
    echo
  fi
done
echo
