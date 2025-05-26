# type: perl response.pl <trace file> <required node>  >   response.out 

$infile=$ARGV[0];
$tonode=$ARGV[1];

$arrival=0;
$departure=0;

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
    $tab[$x[11]]=$tab[$x[11]]+$x[1];
    print STDOUT "$x[1] $x[11] $tab[$x[11]] \n";
}
#checking if the event corresponds to a transmission 
if ($x[0] eq '+') 
{ 
    $arrival=$arrival+1;
    $tab[$x[11]]=-$x[1];
}
}
}
    close DATA;
exit(0);
 
