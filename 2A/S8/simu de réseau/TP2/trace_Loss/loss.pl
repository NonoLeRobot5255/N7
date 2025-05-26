# type: perl length.pl <trace file> <required node>   

$infile=$ARGV[0];
$tonode=$ARGV[1];

#we compute how many bytes were transmitted during time interval specified
#by granularity parameter in seconds
$arrival=0;
$departure=0;
$loss=0;
$drop=0;
$col=0;
$coll=0;
$sum_d=0;
$sum_c=0;
$avr_c=0;
$avr_d=0;

      open (DATA,"<$infile")
        || die "Can't open $infile $!";
  
    while (<DATA>) {
             @x = split(' ');

$lasttime=$x[2];

#column 1 is time 
#checking if the event corresponds to a reception 
if ($x[0] eq 'r') 
{
$departure=$departure+1;
$loss=$drop/$arrival;
$sum_d=$sum_d+$loss;
$avr_d=$sum_d/$arrival;
$thpt_a=$arrival/$x[1];
$rho_a=$thpt_a*0.00084;
$thpt_o=($arrival+$coll)/$x[1];
$rho_o=$thpt_o*0.00084;
$thpt_s=$departure/$x[1];
$rho_s=$thpt_s*0.00084;
print STDOUT "$x[1] $drop $loss $avr_d $coll $col $avr_c $thpt_a $thpt_o $thpt_s $rho_a $rho_o $rho_s\n";
}
if ($x[0] eq '+') 
{ 
$arrival=$arrival+1;
}
if ($x[0] eq 'd') 
{ 
$drop=$drop+1;
$loss=$drop/$arrival;
$sum_d=$sum_d+$loss;
$avr_d=$sum_d/$arrival;
$thpt_a=$arrival/$x[1];
$rho_a=$thpt_a*0.00084;
$thpt_o=($arrival+$coll)/$x[1];
$rho_o=$thpt_o*0.00084;
$thpt_s=$departure/$x[1];
$rho_s=$thpt_s*0.00084;
print STDOUT "$x[1] $drop $loss $avr_d $coll $col $avr_c $thpt_a $thpt_o $thpt_s $rho_a $rho_o $rho_s\n";
}
if ($x[0] eq 'c') 
{ 
$coll=$coll+1;
$col=$coll/($arrival+$coll);
$sum_c=$sum_c+$col;
if ($coll > 0) { $avr_c=$sum_c/$coll; } else {$avr_c=0}
$thpt_a=$arrival/$x[1];
$rho_a=$thpt_a*0.00084;
$thpt_o=($arrival+$coll)/$x[1];
$rho_o=$thpt_o*0.00084;
$thpt_s=$departure/$x[1];
$rho_s=$thpt_s*0.00084;
#print STDOUT "$x[1] $drop $loss $avr_d $coll $col $avr_c $thpt_a $thpt_o $thpt_s $rho_a $rho_o $rho_s\n";
}
}
    close DATA;
exit(0);
 
