#!/usr/bin/env bash

WEBHOST="uwplse.org"
WEBDIR="/var/www/oeuf"
LOG=$(printf "%s-%s-%s-oeuf-hook.txt" \
             "$(TZ="America/Los_Angeles" date "+%y%m%d")" \
             "$(TZ="America/Los_Angeles" date "+%H%M%S")" \
             "$(hostname -s)" \
             )

function main {
  echo
  echo OEUF HOOK CLEANER
  echo
  make cleaner

  echo
  echo OEUF HOOK BUILD
  echo
  make all

  echo
  echo OEUF HOOK TEST
  echo
  bash run_tests.sh
}

(time main) &> "$LOG"
scp "$LOG" "$WEBHOST:$WEBDIR/$LOG"
rm -f "$LOG"
