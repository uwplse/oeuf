#!/usr/bin/env bash

set -e

echo Testing Oeuf...

# may require GNU sed
COQC="coqc $(sed '/^[[:space:]]*$/q' _CoqProject)"

for f in test/*.v
do
# unfortunately this does not correctly handle quoting from _CoqProject,
# so those rules that are necessary are repeated here
    $COQC -Q src "" "$f" >/dev/null 2>&1
    TESTNAME=$(basename "$f" ".v" | tr '[:upper:]' '[:lower:]')
    ./occ.sh "$TESTNAME" >/dev/null 2>&1
    ./a.out > "test/${TESTNAME}.actual"
    if ! diff -q "test/${TESTNAME}.expected" "test/${TESTNAME}.actual"
    then echo "Test $TESTNAME failed!"
         diff -u "test/${TESTNAME}.expected" "test/${TESTNAME}.actual" || true
    else echo "Test $TESTNAME passed!"
    fi
done
