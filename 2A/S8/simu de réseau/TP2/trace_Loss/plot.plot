set xlabel "charge offerte (G)"
set ylabel "charge utilse (rho)"
set title "charge utile en fonction de charge offerte"

plot [0:2] "res.txt" using 12:13 title "simulation" w l
set terminal postscript
set output out.ps
replot
set terminal X11