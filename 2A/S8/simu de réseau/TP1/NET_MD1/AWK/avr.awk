BEGIN { FS = " "} { nl++ } { s=s+$3} END {print s/nl}
