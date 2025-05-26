# type: perl length.pl <trace file> <required node>   

$infile=$ARGV[0];
$tonode=$ARGV[1];

#we compute how many bytes were transmitted during time interval specified
#by granularity parameter in seconds
$arrival=0;
$departure=0;
$nbp=0;
$sum=0;
$sum2=0;
$lasteventtime=0.0;

open (DATA,"<$infile") || die "Can't open $infile $!";
  
while (<DATA>) {
  @x = split(' ');

  #column 1 is time 
  #checking if the destination corresponds to arg 1
  if ($x[3] eq $tonode) 
  { 
    #checking if the event corresponds to a reception 
    if ($x[0] eq 'r') 
    { 
      $delay=$x[1]-$lasteventtime;
      $lasteventtime=$x[1];
      $sum=$sum+($nbp*$delay);
      $sum2=$sum2+$delay*($nbp*$nbp);
      $nbp=$nbp-1;
      $departure=$departure+1;
      $avr=$sum/$lasteventtime;
      $s2=$sum2/$lasteventtime;
      if (($lasteventtime-$delay)>0.0) {
	#$var=($sum2-$lasteventtime*($avr*$avr))/($lasteventtime-$delay);
        $var=($s2-($avr*$avr));
      }
      else
      {
        $var=$x[1];
      }
      $conf=1.96*sqrt(abs($var))/sqrt(abs($lasteventtime));
      $sup=$avr+$conf;
      $inf=$avr-$conf;

      #print STDOUT "$x[1]\t$nbp\t$avr\t$conf\t$inf\t$sup \n";
      printf STDOUT "%13f%10s%13d%13f%13f%13f%13f\n", $x[1],"",$nbp,$avr,$conf,$inf,$sup;
    }
    if ($x[0] eq '+') 
    { 
      $delay=$x[1]-$lasteventtime;
      $lasteventtime=$x[1];
      $sum=$sum+($nbp*$delay);
      $sum2=$sum2+$delay*($nbp*$nbp);
      $nbp=$nbp+1;
      $arrival=$arrival+1;
      $avr=$sum/$lasteventtime;
      $s2=$sum2/$lasteventtime;
      if (($lasteventtime-$delay)>0.0) {
	#$var=($sum2-$lasteventtime*($avr*$avr))/($lasteventtime-$delay);
        $var=($s2-($avr*$avr));
      }
      else
      {
        $var=$x[1];
      }
      $conf=1.96*sqrt(abs($var))/sqrt(abs($lasteventtime));
      $sup=$avr+$conf;
      $inf=$avr-$conf;

      printf STDOUT "%13f%10s%13d%13f%13f%13f%13f\n", $x[1],"",$nbp,$avr,$conf,$inf,$sup;
      #print STDOUT "$x[1]\t$nbp\t$avr\t$conf\t$inf\t$sup\n";
    }
  }
}
#$meanlength=$sum/$lasteventtime;
#print STDOUT "Nombre moyen de clients: $meanlength  \n";
close DATA;
exit(0);
 
