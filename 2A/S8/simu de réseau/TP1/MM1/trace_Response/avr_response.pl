# type: perl avr_response.pl <trace file>  >   avr_response.out 
# Ca genere un fichier avec temps_evenement:id_paquet:temps_de_reponse:nv_moyenne:taille_de_l_intervalle_de_confiance:borne_inf:borne_sup

$infile=$ARGV[0];
$tonode=$ARGV[1];

$arrival=0;
$departure=0;
$sum=0.0;
$sum2=0.0;


open (DATA,"<$infile") || die "Can't open $infile $!";
#printf STDOUT "#%15s%10s%15s%15s%15s%15s%15s\n", "time_evt","id_pkt","time_resp","mean","size_interval","borne_inf","borne_sup";
#print STDOUT "#time_evt\tid_pkt\ttime_resp\tmean\tsize_interval\tborne_inf\tborne_sup\n";

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
  } else {
    $var=$x[2];
 }
 $conf=1.96*sqrt(abs($var))/sqrt(abs($departure));
 $sup=$avr+$conf;
 $inf=$avr-$conf;
 printf STDOUT "%13f%10d%13f%13f%13f%13f%13f\n", $x[0],$x[1],$x[2],$avr,$conf,$inf,$sup;
	     
}

close DATA;
exit(0);
 
