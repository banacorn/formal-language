#!/usr/bin/env sh

# wait for
#   nc -zv localhost 1531
# from vim

while [ 1 ]
do
    echo "=============================="
    filename=`nc -l 1531 | sed "s/;//g" | sed "s/ //g"`
    filepath="`pwd -P`/$filename"
    date
    echo "Input file: $filepath"
    agda $filepath
    echo "All Goals:"
    echo "IOTCM \"$filepath\" NonInteractive Indirect (Cmd_load \"$filepath\" [])" | agda --interaction | grep "All Goals" | sed 's/(agda2-info-action ".All Goals." "\(.*\)" nil)/\1/' | sed 's/\\n/\
/g' | awk '{ if ($0 != "") {print "  " $0}}'
done

