# type: perl detailedresponse.pl <trace file> <required node> <granlarity>   >    output file

$infile=$ARGV[0];
$tonode=$ARGV[1];
$granularity=$ARGV[2];

#we compute how many bytes were transmitted during time interval specified
#by granularity parameter in seconds
$sum=0;
$sum1=0;
$clock=0;
$arrival=0;
$departure=0;

      open (DATA,"<$infile")
        || die "Can't open $infile $!";
  
    while (<DATA>) {
             @x = split(' ');

#column 1 is time 
if ($departure-$clock <= $granularity)
{
#    print STDOUT "$arrival\n";
#checking if the destination corresponds to arg 1
if ($x[3] eq $tonode) 
{ 
#checking if the event corresponds to a reception 
if ($x[0] eq 'r') 
{ 
    $sum=$sum+$x[1];
    $departure=$departure+1;
    $tab[$x[11]]=$tab[$x[11]]+$x[1];
    print STDOUT "$x[1] $x[11] $tab[$x[11]] \n";
}
if ($x[0] eq '+') 
{ 
    if ($arrival <= $granularity) {
    $sum=$sum-$x[1];
    $tab[$x[11]]=-$x[1];
    $arrival=$arrival+1;
    }
    else {
    $sum1=$sum1-$x[1];
    $tab[$x[11]]=-$x[1];
    $arrival=$arrival+1;
    }
}
}
}
else
{   $throughput=$sum/$granularity;
    # print STDOUT "$x[1] $throughput $arrival $departure\n";
    $clock=$clock+$granularity;
    $sum=$sum1;
    $sum1=0;
    #  $departure=0;
    $arrival=$arrival-$granularity;
}   
}
   $throughput=$sum/$granularity;
   # print STDOUT "$x[1] $throughput\n";
    $clock=$clock+$granularity;
    $sum=0;
    # $departure=0;
    $arrival=0;

    close DATA;
exit(0);
 
