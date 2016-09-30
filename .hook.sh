#!/usr/bin/env bash

WEBHOST="uwplse.org"
WEBDIR="/var/www/oeuf/logs"
LOG=$(printf "%s-%s-%s-oeuf-hook.txt" \
             "$(TZ="America/Los_Angeles" date "+%y%m%d")" \
             "$(TZ="America/Los_Angeles" date "+%H%M%S")" \
             "$(hostname -s)")

METRICS=$(printf "%s-%s-metrics.json" \
             "$(TZ="America/Los_Angeles" date "+%y%m%d")" \
             "$(TZ="America/Los_Angeles" date "+%H%M%S")")

function main {
  echo ---------------------
  echo OEUF HOOK CLEANER
  echo ---------------------
  make cleaner

  echo ---------------------
  echo OEUF HOOK DEPS
  echo ---------------------
  pushd ../StructTact/ \
    && git pull \
    && make clean \
    && ./configure \
    && make
  popd

  pushd ../PrettyParsing/ \
    && git pull \
    && make clean \
    && ./configure \
    && make
  popd

  echo ---------------------
  echo OEUF HOOK COMPCERT
  echo ---------------------
  make compcert

  echo ---------------------
  echo OEUF HOOK CONFIGURE
  echo ---------------------
  ./configure

  echo ---------------------
  echo OEUF COQ PLUGIN
  echo ---------------------
  make plugin
  
  echo ---------------------
  echo OEUF HOOK BUILD
  echo ---------------------
  make #will fail
  make sanitize #cleanup
  make

  echo ---------------------
  echo OEUF HOOK TEST
  echo ---------------------
  make test
}

(time main) &> "$LOG"
scp "$LOG" "$WEBHOST:$WEBDIR/$LOG"

ALL_PASS="ALL TESTS PASSED"
PASSED=`grep "$ALL_PASS" "$LOG" | wc -l`
ZERO="0"
if [[ $PASSED -gt $ZERO ]] ; then
    echo "Successful normal build"
else
    echo "Problematic build"
    bash .notify.sh "$LOG"
fi

sh make_metrics.sh
cp metrics.json "$METRICS$
scp metrics.json "$WEBHOST:$WEBDIR/$LOG"
scp "$METRICS" "$WEBHOST:$WEBDIR/$LOG"


rm -f "$LOG"
rm -f "$METRICS"
