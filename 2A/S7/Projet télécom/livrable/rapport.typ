#import "../../../../template/template_2A.typ": *

#show: project.with(

  title : "Rapport du projet de télécommunications",
  authors: ("MIELCAREK Titouan", "MARTIN Nolann"),
  teachers: ("ESCRIG Benoit", "THOMAS Natalie"),
  year: "2024-2025",
  profondeur: 2,
) 

= Introduction

Dans ce projet, le but est de simuler une chaine complète de modulation et démodulation de la chaine DVB-S. Pour cela nous procéderons étaps par étape en rajoutant à chaque fois un élément de la chaine de transmission.

Nous utiliserons pour cela la norme DVB-S, c'est pou cela que nous utiliserons dans un premier temps le paramètre suivant:

- $R_b = 84.4*10^6$ 
- nb_bits = 188*8*5000 (il nous faut des paquets de 188 octets et nous conformisons a 5000 paquets pour avoir un nombre de bits correct et des simulations cohérentes) pour la plus part des simulations.
  
Tous les autres paramètres se déduisent de celui-ci.

Et pour le fitlre nous utiliserons un cosinus surelevé de facteur de surechantillonnage $alpha = 0.35$. Nous utiliserons ce filtre car c'est un filtre de type RIF.
= Implantation du modulateur/démodulateur

Nous implenterons ici une chaine de transmission QPSK comme déjà réalisé dans le projet de télécom de l'an dernier.

== Etude théorique de la modulation QPSK

=== Schéma de la chaine de tranmission associé à une modulation QPSK 
Voici le schéma de la chaine de transmission associé à une modulation QPSK avec sa chaine passe bas équivalent.
#figure(image("../screen/chaine de transmission.png",width: 80%))
Et voici le schéma de la chaine de transmission associé à une modulation QPSK avec sa chaine passe bas équivalent.
#figure(image("../screen/passe bas equivalent.png",width: 80%))

=== Facteur de suréchantillonnage minimal à utiliser

Pour une modulation QPSK, le facteur de suréchantillonnage minimal à utiliser si nous respectons le citère de Shannon est de :

$N_s = T_s/T_e\
N_s >= T_s *2B\
N_s >= T_s *(2(1+alpha))/T_s\
N_s >= 2(1+alpha)\
N_s >= 2.7\  
$


Nous prendrons donc un facteur de suréchantillonnage un peu supérieur à 2, ce qui correspond pour un facteur de surechantillonnage de DVB-S de 5.
=== efficacité spectrale théorique

L'efficacité spectrale théorique est donnée par la formule suivante:

- $R_b/B_w = 1/(1+alpha) = 1/(1+0.35) = 0.74$

== Implantation 

Nous implantons ici le modulateur et le démodulateur QPSK. Nous n'aurons pas de bruit dans un premier temps. Nous avons donc une chaine de transmission "parfaite". Et un TEB nul, car aucun bruit et que nous avons le filtrage adapté.

#figure(image("../screen/TEB_nul.png",width: 20%))
#pagebreak()
== Ajout du bruit 


=== Comparaison entre le TEB théorique et le TEB simulé
Dans cette partie nous ajoutons du bruit à notre chainde de transmission, nous aurons un canal AWGN. Nous allons donc calculer le TEB en fonction du SNR. Pour cela nous prendrons un SNR de -4 à 4 dB.
Nous pouvons donc apercevoir cette courbe:

#figure(image("../screen/QPSK_bruit.png",width: 80%), caption: "nb_bits = 10000000 et Teb théorique = "+ $Q(sqrt(2(E_b/N_0)))$)

Nous voyons bien que la courbe est en accord avec la courbe théorique. Nous avons donc bien implanté notre chaine de transmission.


=== Précision de notre TEB

Nous devons donc calculer la précision de notre TEB, pour cela nous allons faire la démarche inverse, on trouve un nombre d'erreur qui fixera notre précision et ensuite nous calculerons un TEB dessus. 

Nous fixons le nombre d'erreur à 4 ce qui nous fais un précision de $1/2$ et avec un $E_b/N_0 = 10$, nous faisons donc tourner notre simulation en envoyant des trames jusqu'à avoir 4 erreurs. Nous obtenons donc un TEB de l'ordre de $10^(-6)$ en ayant des trames de $10000$ bits. Nous pouvons donc dire qu'avec une précision de $1/2$ nous avons un TEB de l'ordre de $10^(-6)$.

=== Optimalité de notre chaine de transmission

Nous pouvons dire que notre chaine est optimal par plusieurs points:
- Le filtrage est adapté
- Le critère de Shannon est respecté


#pagebreak()
= Ajout du codage canal 

Dans cette partie nous allons ajouter un codage canal à notre chaine de transmission. Nous allons nous baser sur les standards DVB-S.

=== Étude du codage convolutif sous matlab 

Nous avons dans un premier temps étudier comment utiliser du codage convolutif sous matlab.
Nous avons donc appris en mettant en place un code convolutif de paramètre $(3,1/2)$ avec les polynomes générateurs suivants:

- $g_1 = 5_{10} = 101_{2}$
- $g_2 = 7_{10} = 111_{2}$
  
Et avons obtenus un treillis de la forme suivante:

#figure(image("../screen/treillis_exemple.png",width: 80%))
Et comprenons bien le fonctionnement du code convolutif a travers ce treillis.

== Ajout du codage canal à notre chaine de transmission 
=== Codage canal simple
Dans cette deuxième partie nous allons donc utiliser le code convolutif de paramètre $(7,1/2)$ avec les polynomes générateurs suivants: 

- $g_1 = 171_{10} = 10101011_{2}$
- $g_2 = 133_{10} = 10000101_{2}$

précisé dans les standards DVB-S, nous pouvons sortir de ce codage un treillis : 

#figure(image("../screen/treillis.png",width: 80%))

Beaucoup plus difficile à comprendre... Gardons à l'ésprit que c'est un code de rendement 1/2, donc nous avons un bit d'entrée pour deux bits de sortie. Afin de minimiser les erreurs quand nous décodons notre signal.
Pour ce faire, nous décoderons de deux manières différentes :
- décodage hard, dans le quel nous utilisons la distance euclidienne pour décider de la valeur de nos bits
- décodage soft, dans le quel nous utilisons la distance de Hamming pour décider de la valeur de nos bits. Nous y utiliserons l'algorithme de Viterbi pour décoder.

Nous traçons donc le TEB en fonction du SNR pour ce nouveau codage. Nous obtenons la courbe suivante:

#figure(image("../screen/codage_canal.png",width: 80%), caption: "nb_bits = 188*8*5000 et Teb théorique = "+ $Q(sqrt(2(E_b/N_0)))$)

Nous voyons plusieurs choses:

+ Le décodage soft à l'air meilleur que le décodage hard.
  - Le décodage soft est plus précis que le décodage hard car il prend en compte la distance de Hamming et non la distance euclidienne, ce qui fait que les petites distances sont plus prises en compte et pas directement affilié à un 1 ou un 0.
+ en dessous de -1 dB, notre TEB de notre chaine QPSK de base est meilleur que notre chaine avec codage canal (que ça soit en décodage hard ou soft).
  - Cela est dû au fait que a très bas SNR, le codage canal n'est pas efficace, car le bruit est trop fort et le codage ne peut pas le corriger. Encore pire, il rajoute des erreurs en essayant de les corriger.
+ Nous ne voyons pas de fin à notre courbe pour le décodage soft.
  - Cela est dû au fait que nous n'avons pas simulé avec assez de bits pour voir aparaitre une erreur. Nous retrouverons ce problème sur nos futurs simulations mais ne le réécpliquerons pas à chaque fois.

Nous pouvons donc conclure sur cette partie que le codage canal est efficace pour des SNR supérieurs à -1 dB, mais en dessous de cette valeur, il est moins efficace que notre chaine de base. De plus le décodage soft est plus efficace que le décodage hard.

=== Codage canal avec poinçonnage 
Nous pouvons facilement comprendre qu'avec un codage canal simple, le taux de codage de $1/2$ impose une efficacité spectrale plus basse, nous transmettons moins d'information pour la même bande passante. Nous pouvons, afin de remédier à ça utiliser un code poiçonner. Nous allons donc utiliser un code poiçonner afin de passer à un rendement de $2/3$,pour cela nous aurons la matrice de poiçonnage $P = [1101]$.

nous aurons un TEB un peu plus élevé mais notre efficacité spectrale sera bien meilleur. Ce qui permet de transmettre plus d'information pour la même bande passante. Nous obtenons donc cette courbe de TEB : 

#figure(image("../screen/poiconnage.png",width: 80%), caption: "nb_bits = 188*8*5000 et Teb théorique = "+ $Q(sqrt(2(E_b/N_0)))$)

Cette courbe valide bien notre hypothèse, nous avons ici un TEB un peu plus élevé mais nous avons vu précédemment que l'efficacité spectrale est meileure. 

Nous pouvons noter que le poiçonnage ne serait pas viable en cas de décodage hard car prenant la distance euclidienne, nous ne prendrons que des mauvaises décisions sur nos poiçons avec le bruit qui y est introduit, ou en tous cas hasardeuses. C'est pour cela que nous utilisons le décodage soft. 

#pagebreak()
== Introduction du code bloc de Reed Solomon

Dans cette partie nous allons introduire un code de Reed Solomon à notre chaine de transmission. Un code de Reed Solomon est un code correcteur d'erreur qui permet de corriger des erreurs de burst. Pour ce faire il rajoute des bits de redondance à notre signal. Nous pourrions donc ajouter un code RS de paramètre $(255,223)$ à notre chaine de transmission mais nous utiliserons plutôt sa version réduite $(204,188)$. Ce code a une capacité de correction d'erreur de :

$t = (n-k)/2\ 
t = (204-188)/2\
t = 8$

Nous avons donc des blocs de 188 symboles d'information et 16 symboles de redondance corriger 8 symboles d'erreurs. C'est ce code qui est utilisé dans les standards DVB-S. Après implantation nous pouvons observer cette courbe de TEB en fonction du SNR:

#figure(image("../screen/RS.png",width: 80%), caption: "nb_bits = 188*8*5000 et Teb théorique = "+ $Q(sqrt(2(E_b/N_0)))$)

Nous pouvons voir que le code RS pour un SNR très faible, à un TEB qui se superpose à celui du codage canal avec poiçonnage, mais pour un SNR plus au dessus de 0 environ, les deux courbes se séparent et le code RS est plus efficace. Nous pouvons en dire que le code RS à faible SNR ne peux pas corriger les erreurs car les burst sont trop longs, mais à partir d'un certain SNR, les groupements d'erreurs sont plus courts ($<= 8$)et le code RS peut les corriger et ainsi améliorer le TEB. 

Nous pouvons donc conclure que le RS est efficace et corrige bien les burst d'erreurs sufisament petits qui sont fréquents en condition rééels. De plus le couplage entre le RS et le codage canal avec poiçonnage est efficace car le codage canal corrige les erreurs isolées et le RS les burst d'erreurs.

#pagebreak()

== Introduction de l’entrelaceur convolutif (DVB-S)

Dans cette partie nous ajoutons un entrelaceur convolutif, qui est un procéder qui permet de mélanger les octets d'informations afin de répartir les erreurs sur l'ensemble du signal, c'est la règle du "diviser pour mieux régner". Pour ce faire dans la documentation de DVB-S nous pouvons voir que l'entrelaceur est de taille $I = 12$ et de profondeur $L = 17$. Nous avons donc un entrelaceur de taille 12 et de profondeur 17. Qui introduit un retard de :

$D = L*I*(I-1)\
D = 17*12*11\
D = 2244 "octets"$ 

Nous devrons donc prendre ce retard en compte et corriger ce retard afin de ne pas avoir de TEB égal à 0.5 (qui représente une décision "aléatoire"). Mais en prenant tout ça en compte nous pouvons donc observer cette courbe de TEB en fonction du SNR:

#figure(image("../screen/DVBS.png",width: 80%), caption: "nb_bits = 188*8*5000 et Teb théorique = "+ $Q(sqrt(2(E_b/N_0)))$)

Nous pouvons voir que pour un SNR très bas le DVB-S complet ne se démarque pas de tout le reste mais que assez rapidement, pour un SNR de 1 dB, l'entrelaceur vient séparer ses erreurs et aider le code convolutif et le code de Reed Solomon à corriger des erreurs trop en grappe. Nous voyons comme dit au début que pour un SNR de 1.5 seulement, sur nos 5000 paquets de 188 octets, aucune erreur n'a été faite car la courbe n'est pas tracé, ce qui montre que très rapidement DVB-S corrige toutes les erreur même dans un grand volume de bits à transmettre.

De plus comme pour notre modulation en bande de base, nous pouvons calculer la précision, avec la même démarche que pour notre modulation en bande de base, malheuresment à un $E_b/N_0 = 10$ nous ne détéctons plus d'erreur même avec $1*10⁹$ bits envoyés. Nous ne pouvons donc pas conclure sur la précision de notre TEB mais pouvons affirmer que nous avons un bien meilleur TEB que pour notre modulation en bande de base.
#pagebreak()
= Conclusion 

== Toutes les courbes de TEB en fonction du SNR

#figure(image("../screen/TEB.jpg",width: 80%),caption: "nb_bits = 188*8*20000 et Teb théorique = "+ $Q(sqrt(2(E_b/N_0)))$)
Nous pouvons voir sur cette simulation avec un nombre de bits plus important que toutes les précédentes que le DVB-S est bien plus efficace que les autres modulations pour un SNR au dessus de 1 dB.Nous pouvons voir que toutes le courbes de codage canal sont meilleures que la courbe du TEB du QPSK bande base pour un SNR au dessus de 0.

== Conclusion générale

Pour conclure, nous avons étudier ici toutes les étapes pour implanter DVB-S et avons simulé sur matlab la chaine complète en étudiant chaque étape de son implantation, nous avons pû voir de plus que à un SNR très faible le codage canal n'a pas d'intérêt dû au trop fort bruit par rapport à notre signal. De plus d'après des recherches dont les résultats sont à prendre avec des pincettes, à l'époque de la création de DVB-S le niveau de bruit se situait entre 3 et 15 dB, ce qui montre que DVB-S serait meilleur à ce niveau de bruit que tous les autres systèmes de transmission étudiés ici. Aujourd'hui le niveau de bruit est bien plus faible et DVB-S est donc un système de transmission très efficace. Même si aujourd'hui DVB-S est en grande partie remplacé par DVB-S2, qui est une amélioration de DVB-S.