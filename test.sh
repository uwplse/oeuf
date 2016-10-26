#!/usr/bin/env bash

set -e

echo Testing Oeuf...

# may require GNU sed
COQC="coqc $(sed '/^[[:space:]]*$/q' _CoqProject)"

PASSED=true

for f in test/*.v ; do
# unfortunately this does not correctly handle quoting from _CoqProject,
# so those rules that are necessary are repeated here
    $COQC -Q src "" "$f" >/dev/null 2>&1 || { echo "coqc failed on $f"; exit 1; }
    TESTNAME=$(basename "$f" ".v" | tr '[:upper:]' '[:lower:]')
    ./occ.sh "$TESTNAME" || { echo "occ.sh failed on $TESTNAME"; exit 1; }
    ./"$TESTNAME" > "test/${TESTNAME}.actual" || { echo "./a.out failed on $TESTNAME"; exit 1; }
    if ! diff -q "test/${TESTNAME}.expected" "test/${TESTNAME}.actual"
    then echo "Test $TESTNAME failed!"
	 PASSED=false
         diff -u "test/${TESTNAME}.expected" "test/${TESTNAME}.actual" || true
    else echo "Test $TESTNAME passed!"
         rm "$TESTNAME.oeuf" "$TESTNAME.o"
         rm "shim.c" "shim.o"
    fi
done

if $PASSED ; then
    echo "ALL TESTS PASSED"
fi
