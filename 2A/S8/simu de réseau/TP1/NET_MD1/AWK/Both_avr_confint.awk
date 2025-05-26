BEGIN { FS = " "} {val[nl]=$3} {nl++} {s=s+$3} END { 
av=s/nl;
print s " " nl " " av;
for (i in val) {
 d=val[i] - av ;
 s2 = s2 + d * d ;  
}
s=sqrt(s2/(nl-1)); 
print "sample variance: " s " Conf. Int. 95%: " av "+/-"1.96*s/sqrt(nl) 
}
