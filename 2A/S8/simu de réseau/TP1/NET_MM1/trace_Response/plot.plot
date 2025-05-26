set terminal png 800,600 enhanced font "Helvetica,20"

set output "node1.png"
set title "title"
plot [0:20] "avr_response1.out" using 1:3 title "instantaneous" w l, "avr_response1.out" using 1:4 title "average" w l, "avr_response1.out" using 1:4:5 w yerrorbars 

set output "file2.png"
plot [0:2000] "avr_response1.out" using 1:3 title "instantaneous response time", "avr_response1.out" using 1:4 title "average" w l, "avr_response1.out" using 1:6 title "confidance interval-inf" w l, "avr_response1.out" using 1:7 title "confidance interval-sup" w l 

set output "file3.png"
plot [0:20] "avr_response2.out" using 1:3 title "instantaneous" w l, "avr_response2.out" using 1:4 title "average" w l, "avr_response2.out" using 1:4:5 w yerrorbars 

set output "file4.png"
plot [0:2000] "avr_response2.out" using 1:3 title "instantaneous response time", "avr_response2.out" using 1:4 title "average" w l, "avr_response2.out" using 1:6 title "confidance interval-inf" w l, "avr_response2.out" using 1:7 title "confidance interval-sup" w l 

