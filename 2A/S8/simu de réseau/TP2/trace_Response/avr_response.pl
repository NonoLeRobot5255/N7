# type: perl avr_response.pl <trace file>  >   avr_response.out 

$infile=$ARGV[0];
$tonode=$ARGV[1];

$arrival=0;
$departure=0;
$sum=0.0;
$sum2=0.0;


      open (DATA,"<$infile")
        || die "Can't open $infile $!";
  
    while (<DATA>) {
             @x = split(' ');

#column 1 is time 
#checking if the destination corresponds to arg 1

$departure=$departure+1;
$sum=$sum+$x[2];
$sum2=$sum2+($x[2]*$x[2]);
$avr=$sum/$departure;
if ($departure>1) {
$var=($sum2-$departure*($avr*$avr))/($departure-1);
}
else
{
    $var=$x[2];
}
$conf=1.96*sqrt($var)/sqrt($departure);
$sup=$avr+$conf;
$inf=$avr-$conf;
print STDOUT "$x[0] $x[1] $x[2] $avr $conf $inf $sup\n";
	     
}
    close DATA;
exit(0);
 
