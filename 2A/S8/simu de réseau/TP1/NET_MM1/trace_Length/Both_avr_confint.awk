BEGIN { FS = " "} {val[nl]=$5} {nl++} {s=s+$5} END { 
av=s/nl;
#print s " " nl " " av;
for (i in val) {
 d=val[i] - av ;
 s2 = s2 + d * d ;  
}
s=sqrt(s2/(nl-1)); 
print "Simulation : Sample variance = " s " Average = " av " +/- "1.96*s/sqrt(nl) " (conf. Interval - 95%)" 
}
