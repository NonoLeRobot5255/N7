#!/bin/bash
gnuplot -persist <<EOF
set title "$2"
plot [0:$1] "trace_Response/avr_response.out" using 1:3 title "instantaneous response time", \
            "trace_Response/avr_response.out" using 1:4 title "average" w l, \
            "trace_Response/avr_response.out" using 1:6 title "confidence interval-inf" w l, \
            "trace_Response/avr_response.out" using 1:7 title "confidence interval-sup" w l
EOF

