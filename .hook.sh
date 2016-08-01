#!/usr/bin/env bash

WEBHOST="uwplse.org"
WEBDIR="/var/www/oeuf"
LOG=$(printf "log-%s-%s.txt" \
             $(TZ="America/Los_Angeles" date "+%y%m%d") \
             $(TZ="America/Los_Angeles" date "+%H%M%S") \
             )

function main {
  echo
  echo HOOKNOOK OEUF CLEANER
  echo
  make cleaner

  echo
  echo HOOKNOOK OEUF BUILD
  echo
  make all

  echo
  echo HOOKNOOK OEUF TEST
  echo
  bash run_tests.sh
}

(time main) &> "$LOG"
scp "$LOG" "$WEBHOST:$WEBDIR/$LOG"
rm -f "$LOG"
