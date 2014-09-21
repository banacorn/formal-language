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
    esc=`printf '\033'`
    echo "IOTCM \"$filepath\" NonInteractive Indirect (Cmd_load \"$filepath\" [])" | agda --interaction | grep "All Goals" | sed 's/(agda2-info-action ".All Goals." "\(.*\)" nil)/\1/' | sed 's/\\n/\
/g' | sed "s/?\([0123456789]*\) \(.*\)$/${esc}[1;31m?\1${esc}[m \2/g" | sed "s/→/${esc}[1;33m→${esc}[m/g" | awk '{ if ($0 != "") {print "  " $0}}'

#?0 : y == z → x == z
#|0 : y == z → x ==|z
done

