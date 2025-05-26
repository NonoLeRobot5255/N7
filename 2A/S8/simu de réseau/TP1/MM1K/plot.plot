set xlabel "k"
set ylabel "P[rejet]"
set logscale y 

plot "res2.txt" using 1:2 title "Analytique" w l , \
 "res2.txt" using 1:3 title "Simulation" w l 

set terminal postscript
set output "out.ps"
replot
set terminal X11