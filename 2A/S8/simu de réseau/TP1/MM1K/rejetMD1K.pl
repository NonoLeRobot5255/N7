#!/usr/bin/perl

$num_args = $#ARGV + 1;
if ($num_args != 3) {
    $lambda=20.0;
    $mu=33.0;
    $duration=15000.0; #sec
} else {
    $lambda=$ARGV[0];
    $mu=$ARGV[1];
    $duration=$ARGV[2];

}

$rho=$lambda/$mu;

#print "Charge: $rho\n";
#print "Capa. file\tTx analy.\tTx simu.\n";

for ($qsize=1; $qsize<=20; $qsize++) {
    		
    #Start simulation to compute practical loss rate
    system("ns md1k.tcl $lambda $mu $duration $qsize >/dev/null 2>&1");

    #Compute practical loss rate
    $loss=`grep ^d outd.tr | grep -c "0 1 udp"`;
    $arrival=`grep ^+ outd.tr | grep -c "0 1 udp"`;
    $pratique=$loss/$arrival;
    
    #Compute theoretical loss rate
    $theorique=($rho**$qsize) * (1-$rho)/(1-($rho**($qsize+1)));   #** = ^ 
   
    #Print results
    print "$qsize\t$theorique\t$pratique\n";
}
exit;
