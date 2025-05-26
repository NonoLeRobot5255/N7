BEGIN { FS = " "} { nl++ } { s=s+$5} END {print s/nl}
