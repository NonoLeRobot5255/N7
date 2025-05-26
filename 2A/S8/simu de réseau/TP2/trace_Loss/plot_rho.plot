#plot [0:20] "avr_response.out" using 1:3 title "instantaneous" w l, "avr_response.out" using 1:4 title "average" w l, "avr_response.out" using 1:4:5 w yerrorbars 
plot [0:100] "loss.out" using 1:11 title "input load" w l, "loss.out" using 1:12 title "offered load" w l, "loss.out" using 1:13 title "output load" w l


#time #drop %loss avr_%drop #coll %col avr_%coll thpt_a thpt_o thpt_s rho_a rho_o rho_s
