#!/bin/bash
gnuplot -persist <<EOF
set title "$2"
plot [0:$1] "trace_Length/length.out" using 1:2 title "instantaneous length", \
            "trace_Length/length.out" using 1:3 title "average" w l, \
            "trace_Length/length.out" using 1:5 title "confidence interval-inf" w l, \
            "trace_Length/length.out" using 1:6 title "confidence interval-sup" w l
EOF
