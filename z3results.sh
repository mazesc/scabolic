#!/bin/bash

directory=$1

for file in $( find $directory -name "*.smt2" | sort -V )
do
  result=$(z3 $file)
  echo $(basename $file)" "$result >> $directory/results.txt
done
