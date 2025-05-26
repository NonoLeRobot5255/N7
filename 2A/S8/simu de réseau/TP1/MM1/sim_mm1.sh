#!/bin/bash

#Parametres de simulation (en format float)
lambda=$1
mu=$2
duration=$3 #sec

echo "Lancement de la simulation"
ns mm1.tcl $lambda $mu $duration >/dev/null 2>&1

echo "Traitement du temps de reponse (tr)"
cd trace_Response
perl response.pl ../out_mm1.tr 1 > response.out      #calcul tr instantane
perl avr_response.pl response.out > avr_response.out #calcul tr moyen
#Affichage entete (pour decrire les champs resultats)
printf "%10s%13s%13s%13s%13s%13s\n" "nb_pkt" "tr_instant" "tr_mean" "int_conf" "borne_inf" "borne_sup"
#Affichage resultat moyen tr (la derniere valeur calculee est la meilleure estimation du tr)
tail -1 avr_response.out | cut -c14-
cd ..

echo "Traitement de la taille des files d'attente (fa)"
cd trace_Length
perl length.pl ../out_mm1.tr 1 > length.out
#Affichage entete (pour decrire les champs resultats)
printf "%10s%13s%13s%13s%13s%13s\n" "" "fa_instant" "fa_mean" "int_conf" "borne_inf" "borne_sup"
#Affichage resultat moyen taille des fa (la derniere valeur calculee est la meilleure estimation de la taille des fa)
tail -1 length.out | cut -c14-
cd ..

echo "Affichage des graphes tr & fa"
./trace_Length/plot.sh $duration "M/M/1"
./trace_Response/plot.sh $duration "M/M/1"
