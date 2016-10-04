#!/usr/bin/env bash

set -e

METRICS="metrics.json"

rm -f $METRICS
touch $METRICS

echo "[" >> $METRICS

FIRST="1"

for f in src/*.v ; do

    if [[ $FIRST == "1" ]] ; then
	FIRST=0
    else
	echo "," >> $METRICS
    fi
    cat >> $METRICS <<EOF
 { "name" : "$f"
 , "count" : $(grep -i "admit" $f | wc -l)
 }
EOF
    
done

echo "]" >> $METRICS
