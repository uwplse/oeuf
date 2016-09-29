#!/usr/bin/env bash

set -e

METRICS="metrics.json"

rm -f $METRICS
touch $METRICS

echo "[" >> $METRICS

for f in src/*.v ; do

    cat >> $METRICS <<EOF
 { "name" : $f
 , "count" : $(grep -i "admit" $f | wc -l)
 },
EOF
    
done

echo "]" >> $METRICS
