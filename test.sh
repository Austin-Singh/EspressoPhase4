#!/bin/bash

GOODTESTS="/home/wsl/EspressoPhase4Testing/Tests/Phase4/Espresso/GoodTests/*"

numOfGood=0
numOfBad=0
total=0

for f in $GOODTESTS
do
    ((total=total+1))
    echo "Processing $f"
    ./espressoc $f > me.txt 2> /dev/null
    ./espressocr $f > ref.txt 2> /dev/null
    diff -u me.txt ref.txt > diff.txt
    if [ -s diff.txt ]; then
            # The file is not-empty.
            ((numOfBad=numOfBad+1))
            echo "BAD TEST"
            cat diff.txt
    else
            # The file is empty.
            ((numOfGood=numOfGood+1))
            echo "GOOD TEST"
    fi
done

echo "$numOfGood of $total passed. (i.e. didn't pass: $numOfBad)"