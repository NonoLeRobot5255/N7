set ns [new Simulator]

set tf [open out_mm1.tr w] 
$ns trace-all $tf

set lambda 30.0
set mu     33.0
set rho $lambda/$mu
set L [expr $rho/(1-$rho)]
set R [expr $L/$lambda]
puts "Theoric Mean Length : $L\n"
puts "Theoric Response Time : $R\n"


set n1 [$ns node]
set n2 [$ns node]
set n3 [$ns node]
# Since packet sizes will be rounded to an integer
# number of bytes, we should have large packets and
# to have small rounding errors, and so we take large bandwidth
set link1 [$ns simplex-link $n1 $n2 100kb 0ms DropTail]
set link2 [$ns simplex-link $n2 $n3 100kb 0ms DropTail]
$ns queue-limit $n1 $n2 100000
$ns queue-limit $n2 $n3 100000

# generate random interarrival times and packet sizes
set InterArrivalTime [new RandomVariable/Exponential]
$InterArrivalTime set avg_ [expr 1/$lambda]
set pktSize [new RandomVariable/Exponential]
$pktSize set avg_ [expr 100000.0/(8*$mu)]

set src [new Agent/UDP]
$src set packetSize_ 100000
$ns attach-agent $n1 $src

# queue monitoring
#set qmon1 [$ns monitor-queue $n1 $n2 [open qm_1.out w] 0.1]
#set qmon2 [$ns monitor-queue $n2 $n3 [open qm_2.out w] 0.1]
#$link1 queue-sample-timeout

proc finish {} {
    global ns tf
    $ns flush-trace 
    close $tf 
    exit 0 
} 

proc sendpacket {} {
    global ns src InterArrivalTime pktSize 
    set time [$ns now]
    $ns at [expr $time + [$InterArrivalTime value]] "sendpacket"
    set bytes [expr round ([$pktSize value])]
    $src send $bytes
}

set sink [new Agent/Null]
$ns attach-agent $n3 $sink
$ns connect $src $sink
$ns at 0.0001 "sendpacket"
$ns at 9000.0 "finish"

$ns run

