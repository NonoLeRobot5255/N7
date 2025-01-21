= CM de codage source

= Introduction

Codage source = coder les bits avant transmission pour réduire les ressources nécessaires à la transmission. 

Codage source $!=$ de codage canal (donner de la redondance pour éviter les erreurs à cause du bruit).

La compression est possbile de deux manières :

- avec distorsion : distorion $tilde.eq$ erreur

  -- Quantificateur : baisser le nombre de bits par échantillons mais on gagne de l'erreur de distorsion. (On le rajoute quand on à de la distorion)

- sans distorsion : basée sur la théorie de l'information de Shannon.

Dans tous les cas on rajoute un codeur entropique (La prof à dit je cite : "ça fait pas de mal de rajouter encore un trucs")

== Taux de compression 

Il n'existe pas de codeur optimal, on doit les comparer pour savoir quel est le meilleur (empirique). On les compare en surtout avec le taux de compression (je crois) : 

- Taux de compression = $"Nombres de symboles en entrées"/"Nombre de symboles à la transmission"$ (c'est la même si on la fait dans l'autre sens)


  -- ex : Fe = 8kHz, B=8bits --> 64kb/s

  si objectif = 2kb/s, on a $64/2$ = 32 en taux de compression

== Notion de distorsion

Différentes définitions de la distorsion :

distorsion = erreur pondérée. Et on à une mesure subjective de la distorsion. (Il existe une mesure objective mais elle est pas pertinente). En mesure subjective on à par exemple le MOS (Mean Opinion Score) qui est une note de 1 à 5, 1 = caca et 5 = woaw. On fait mesurer 24 à 36 experts et on fait la moyenne de leurs résultats.

$x_r - x_e = e(n)$

SNR = $10log((sigma_x²)/(sigma_e²))$ dB 

PSNR = pic signal/noise ratio (elle en a parlé mais osef)

- (erreur moyenne) Distorsion : $sigma_e² = 1/N sum(e(n)²)$

- (avec la puissance) Distorsion : $sigma_e² = integral(s_e (f) "df")$ 

= Codage sans perte ou codage entropique 

== Théorie de l'information

Shannon ce torturé s'est demandé diverses questions : 

- Définition de l'info ?

- Quantifier l'info ? Quantité de l'info ?

Quantité d'info $i(x) = F(p(x))$ p(x) = probabilité que x soit vrai
#pagebreak()
Notion qu'on voulait que la fonction remplisse :
  
  - $F(1) = 0$

  - $p(x)"descend" -->  i(x) "monte"$

  - $i(x_1x_2) = i(x_1)+i(x_2)$

  - $F(P_x_1;P_x_2) = F(P_x_1) + F(P_x_2)$

donc fonction trouvée est :

  - $F(p) = -log(p_x)$

Unité de la quantité d'info = Binary unit (bit) mais c'est pas le bit de l'info. Du coup on peut l'appeler le Shannon

on veut que $- log(1/2) = 1 "bit"$, donc on prend la base 2 du log.

=== Pour résumer :
$i(x) = -log_2(p(x))$

=== Entropie

Entropie d'une source = $H(x) = E(i(x)) = -sum(p(x)log_2(p(x)))$

Entropie :

-  moyenne de quantité d'info ($>0$).

-  incertitude de la source.

- mesure de son imprédictibilité.

Entropie(anglais) < Entropie(Français) < Entropie(Allemand)

*Ensuite on a vu le code de Huffman et comment le faire mais j'avais plus de batterie donc je le mettrais plus tard.*

#pagebreak()

= Codage avec perte 

Décorrélateur = autre façon de representer les données --> mieux adapter a la compression.

Quantificateur = on augmente le TC sans toucher à la distorsion.

La puissance de l'erreur de quantification est proportionnelle à la puissance du signal d'entrée.

erreur de quantification = $epsilon = x(n) - x_q(n)$
 
Pas de quantification :
 -  $sigma_epsilon² = (sigma_x² a^2 2^(-2n))/12 $

$x_R = x + epsilon$

mesure 1 pour quantifier la distorsion : SNR = $10log_10 ((sigma_x²)/(sigma_epsilon²))$

H1 : $epsilon$ bruit de Q : uniforme entre $[-Delta/2;Delta/2]$  --> $sigma_epsilon^2 = Delta^2 /12 $

Dynamique du signal $~ a*sigma_x$

$a*sigma_x = N*Delta = 2^n Delta$

donc $sigma_x^2 = 2^(2n)/a^2 Delta^2$

alors $sigma_x^2/sigma_epsilon^2 = 2^(2n)/a^2 *12 $

et donc $"SNR"= (20 log_10 2)-n ... $

si on veut un TC de n, on à intérer que les données en entrées aient une puissance en entrée plus faible que les données sources.

