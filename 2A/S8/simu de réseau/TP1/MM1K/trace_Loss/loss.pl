# type: perl length.pl <trace file> <required node>   

$infile=$ARGV[0];
$tonode=$ARGV[1];

#we compute how many bytes were transmitted during time interval specified
#by granularity parameter in seconds
$arrival=0;
$departure=0;
$drop=0;

      open (DATA,"<$infile")
        || die "Can't open $infile $!";
  
    while (<DATA>) {
             @x = split(' ');

#column 1 is time 
#checking if the destination corresponds to arg 1
if ($x[3] eq $tonode) 
{ 
#checking if the event corresponds to a reception 
if ($x[0] eq 'r') 
{ 
    $departure=$departure+1;
    $loss=$drop/$arrival;

$sum=$sum+$loss;
$sum2=$sum2+($loss*$loss);
$avr=$sum/$arrival;
if ($arrival>1) {
$var=($sum2-$arrival*($avr*$avr))/($arrival-1);
}
else
{
    $var=$loss;
}
$conf=1.96*sqrt($var)/sqrt($arrival);
$sup=$avr+$conf;
$inf=$avr-$conf;
print STDOUT "$x[1] $drop $loss $avr $conf $inf $sup\n";
}
if ($x[0] eq '+') 
{ 
    $arrival=$arrival+1;
$loss=$drop/$arrival;
}
if ($x[0] eq 'd') 
{ 
    $drop=$drop+1;
$loss=$drop/$arrival;

$sum=$sum+$loss;
$sum2=$sum2+($loss*$loss);
$avr=$sum/$arrival;
if ($arrival>1) {
$var=($sum2-$arrival*($avr*$avr))/($arrival-1);
}
else
{
    $var=$loss;
}
$conf=1.96*sqrt($var)/sqrt($arrival);
$sup=$avr+$conf;
$inf=$avr-$conf;
print STDOUT "$x[1] $drop $loss $avr $conf $inf $sup\n";
}
}
}
#$meanlength=$sum/$lasteventtime;
#print STDOUT "Nombre moyen de clients: $meanlength  \n";
    close DATA;
exit(0);
 
