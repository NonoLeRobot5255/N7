set ns [new Simulator]

set lambda [lindex $argv 0]
set mu [lindex $argv 1]
set duration [lindex $argv 2]
set qsize [lindex $argv 3]

puts "ns: $qsize"

set tf [open outm.tr w] 
$ns trace-all $tf

set n1 [$ns node]
set n2 [$ns node]

set link [$ns simplex-link $n1 $n2 100kb 0ms DropTail]
$ns queue-limit $n1 $n2 $qsize

# generate random interarrival times and packet sizes
set InterArrivalTime [new RandomVariable/Exponential]
$InterArrivalTime set avg_ [expr 1.0/$lambda]
#set pktSize [new RandomVariable/Exponential]
#$pktSize set avg_ [expr 100000.0/(8.0*$mu)]
set pktSize [expr 100000.0/(8.0*$mu)]

Queue/DropTail set mean_pktsize_ 100000.0*8.0
set src [new Agent/UDP]
$src set packetSize_ 100000
$ns attach-agent $n1 $src

# queue monitoring
#set qmon [$ns monitor-queue $n1 $n2 [open qm.out w] 0.1]
#$link queue-sample-timeout

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
    set bytes [expr round ($pktSize)]
    $src send $bytes
    puts "time:$time"
}

set sink [new Agent/Null]
$ns attach-agent $n2 $sink
$ns connect $src $sink
$ns at 0.0001 "sendpacket"
$ns at $duration "finish"

$ns run

