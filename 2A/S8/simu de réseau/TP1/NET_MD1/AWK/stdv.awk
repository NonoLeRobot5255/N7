BEGIN {FS=" "}{ln++}{d=$5-t}{s2=s2+d*d} END {print "standev:" sqrt(s2/ln)}
