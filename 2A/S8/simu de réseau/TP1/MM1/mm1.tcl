set ns [new Simulator]

set lambda    [ lindex $argv 0 ]
set mu        [ lindex $argv 1 ]
set duration  [ lindex $argv 2 ]

set trace_file [open out_mm1.tr w] 
$ns trace-all $trace_file

set n1 [$ns node]
set n2 [$ns node]

# Since packet sizes will be rounded to an integer
# number of bytes, we should have large packets and
# to have small rounding errors, and so we take large bandwidth
set link [$ns simplex-link $n1 $n2 100kb 0ms DropTail]
$ns queue-limit $n1 $n2 100000

# generate random interarrival times and packet sizes
set InterArrivalTime [new RandomVariable/Exponential]
$InterArrivalTime set avg_ [expr 1/$lambda]
set pktSize [new RandomVariable/Exponential]
$pktSize set avg_ [expr 100000.0/(8*$mu)]

set src [new Agent/UDP]
#$src set packetSize_ 100000
$ns attach-agent $n1 $src

# queue monitoring
#set qmon [$ns monitor-queue $n1 $n2 [open qm_mm1.out w] 0.1]
#$link queue-sample-timeout

proc finish {} {
    global ns trace_file
    $ns flush-trace 
    close $trace_file 
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
$ns attach-agent $n2 $sink
$ns connect $src $sink
$ns at 0.0001 "sendpacket"
$ns at $duration "finish"

$ns run
