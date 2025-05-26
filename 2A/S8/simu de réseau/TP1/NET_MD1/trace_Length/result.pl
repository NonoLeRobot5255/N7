#!/usr/bin/perl

$lambda=20;
$mu=33;
$rho=$lambda/$mu;

$L=$rho/(1-$rho);
$R=$L/$lambda;
print "M/M/1\n"; 
print "Analytical : L=$L R=$R\n"; 
$MOY_MM1=`awk -f avr.awk qm_mm1.out`;
#print "$MOY_MM1\n";
#exec `awk -v t=$MOY_MM1 -f ConfInt.awk qm_mm1.out`;
print `awk -f Both_avr_confint.awk qm_mm1.out`;
print "\n";

$L=$rho*(2-$rho)/(1-$rho)/2;
$R=$L/$lambda;
print "M/D/1\n"; 
print "Analytical : L=$L R=$R\n"; 
$MOY_MD1=`awk -f avr.awk qm_md1.out`;
#print "$MOY_MD1\n";
#exec `awk -v t=$MOY_MD1 -f ConfInt.awk qm_md1.out`;
print `awk -f Both_avr_confint.awk qm_md1.out`;
