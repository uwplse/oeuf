#!/usr/bin/env bash

set -e

echo Testing Oeuf...

# may require GNU sed
COQC="coqc $(sed '/^[[:space:]]*$/q' _CoqProject)"

f="test/${1}.v"

$COQC -Q src "" "$f" >/dev/null 2>&1 || { echo "coqc failed on $f"; exit 1; }
TESTNAME=$(basename "$f" ".v" | tr '[:upper:]' '[:lower:]')
./occ.sh "$TESTNAME" || { echo "occ.sh failed on $TESTNAME"; exit 1; }
./"$TESTNAME" > "test/${TESTNAME}.actual" || { echo "./a.out failed on $TESTNAME"; exit 1; }
if ! diff -q "test/${TESTNAME}.expected" "test/${TESTNAME}.actual"
then echo "Test $TESTNAME failed!"
     PASSED=false
     diff -u "test/${TESTNAME}.expected" "test/${TESTNAME}.actual" || true
else echo "Test $TESTNAME passed!"
     #rm -f "$TESTNAME.oeuf" "$TESTNAME.o"
     #rm -f "shim.c" "shim.o"
fi
