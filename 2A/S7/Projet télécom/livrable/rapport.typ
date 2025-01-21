#import "../../../template/template_2A.typ": *

#show: project.with(

  title : "Rapport du projet de télécommunications",
  authors: ("MIELCAREK Titouan", "MARTIN Nolann"),
  teachers: ("ESCRIG Benoit", "THOMAS Natalie"),
  year: "2024-2025",
  profondeur: 1,
) 

= Introduction

Dans ce projet, le but est de simuler une chaine complète de modulation et démodulation de la chaine DVB-S. Pour cela nous procéderons étaps par étape en rajoutant à chaque fois un élément de la chaine de transmission.

Nous utiliserons pour cela la norme DVB-S, c'est pou cela que nous utiliserons dans un premier temps le paramètre suivant:

- $R_b = 84.4*10^6$ 
  
Tous les autres paramètres se déduisent de celui-ci.

Et pour le fitlre nous utiliserons un cosinus surelevé de facteur de surechantillonnage $alpha = 0.35$. Nous utiliserons ce filtre car c'est un filtre de type RIF.
= Implantation du modulateur/démodulateur

Nous implenterons ici une chaine de transmission QPSK comme déjà réalisé dans le projet de télécom de l'an dernier.

== Schéma de la chaine de tranmission associé à une modulation QPSK 
Voici le schéma de la chaine de transmission associé à une modulation QPSK avec sa chaine passe bas équivalent.
#figure(image("../screen/chaine de transmission.png",width: 80%))
Et voici le schéma de la chaine de transmission associé à une modulation QPSK avec sa chaine passe bas équivalent.
#figure(image("../screen/passe bas equivalent.png",width: 80%))

== Facteur de suréchantillonnage minimal à utiliser

Pour une modulation QPSK, le facteur de suréchantillonnage minimal à utiliser si nous respectons le citère de Shannon est de :

 $T_s/T_e = (log_2(M)*T_b)/(1/F_e)\ 
 = log_2(M)* T_b *1/T_b \ 
 = log_2(M) = 2$

Nous prendrons donc un facteur de suréchantillonnage un peu supérieur à 2, ce qui correspond au facteur de surechantillonnage de DVB-S qui est de 5.
== efficacité spectrale théorique

L'efficacité spectrale théorique est donnée par la formule suivante:

- $R_b/B_w = 1/(1+alpha) = 1/(1+0.35) = 0.74$

== Implantation 

Nous implantons ici le modulateur et le démodulateur QPSK. Nous n'aurons pas de bruit dans un premier temps.
