#plot [0:20] "avr_response.out" using 1:3 title "instantaneous" w l, "avr_response.out" using 1:4 title "average" w l, "avr_response.out" using 1:4:5 w yerrorbars 
plot [0:10000] "loss.out" using 1:3 title "drop probability" w l, "loss.out" using 1:4 title "average" w l, "loss.out" using 1:6 title "confidance interval-inf" w l, "loss.out" using 1:7 title "confidance interval-sup" w l 
