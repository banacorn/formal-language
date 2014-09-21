#!/usr/bin/env sh

# wait for
#   nc -zv localhost 1531
# from vim

while [ 1 ]
do
    echo "=============================="
    filename=`nc -l 1531 | sed "s/;//g" | sed "s/ //g"`
    date
    echo "Input file: $filename"
    agda $filename
done
