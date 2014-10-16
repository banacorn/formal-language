#!/usr/bin/env sh

# wait for
#   nc -zv localhost 1531
# from vim

while [ 1 ]; do
    printf "=============================="
    #filename=`nc -l 1531 | sed "s/;//g" | sed "s/ //g"`
    filepath=`nc -l 1531 | sed "s/;//g" | sed "s/ //g"`
    #filepath="`pwd -P`/$filename"
    echo ""
    date
    echo "Input file: $filepath"
    echo "IOTCM \"$filepath\" NonInteractive Indirect (Cmd_load \"$filepath\" [])" | agda --interaction | python process_agda_output.py

done

