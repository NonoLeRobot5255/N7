#plot [0:20] "avr_response.out" using 1:3 title "instantaneous" w l, "avr_response.out" using 1:4 title "average" w l, "avr_response.out" using 1:4:5 w yerrorbars 
plot [0:1000] "length.out" using 1:2 title "instantaneous length", "length.out" using 1:3 title "average" w l, "length.out" using 1:5 title "confidance interval-inf" w l, "length.out" using 1:6 title "confidance interval-sup" w l 
