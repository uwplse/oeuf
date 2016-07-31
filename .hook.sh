#!/usr/bin/env bash

WEBDIR="/var/www/oeuf"

LOG=$(printf "%s/log-%s-%s.txt" \
             "$WEBDIR" \
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

if [ -w "$WEBDIR" ]; then
  main &> "$LOG"
fi
