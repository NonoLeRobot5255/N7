#import "../../../../../template/templatetest.typ": *

#show: project.with(
  
  title: "Rapport de télécomunication",
  authors: (
    "MARTIN Nolann",
    "ARRIX Baptiste",
  ),
)

= Introduction

Ce document est le rapport du projet de télécommunication de première année de l'ENSEEIHT. Nous avions pour objectif construire et comparer différents mappings tel que QSPK,ASK, passes-bas ???

= I : Implantation d’une transmission avec transposition de fréquence

== Tracé des signaux générés sur les voies en phase et en quadrature et tracé du signal transmis

#figure(
  image("Tracé1.1.png", width: 80%),
  caption: [
    Tracé de la voie en phase avec 16 bits et un span de 4.
  ],
)<phase1>
#figure(
  image("Tracé1.2.png", width: 80%),
  caption: [
    Tracé de la voie en quadrature du signal avec 16 bits et un span de 4.
  ],
)<quadrature1>

On voit sur les deux illustrations, les bits transmis ont un retard du au span du cosinus surélevé. 
Nous voyons que l'amplitude entre les symboles reçu et transmis est différente, celà vient de la fréquence porteuse et du retour retour en bande de base. 

== Tracé de la densité spectrale de puissance du signal transmis sur fréquence porteuse.

#figure(
  image("Tracé1.3.png", width: 80%),
  caption: [
    Densité spectrale de puissance du signal transmis sur fréquence porteuse avec 10000 bits.
  ])<DSPporteuse1>

  Nous pouvous voir deux pics, qui sont du au fait que nous passons sur porteuse, ce qui augmente la fréquence de notre densité spectrale de puissance initialement centré autour de 0, la densité spectrale de puissance étant symétrique, un deuxième pic apparait bien sur notre @DSPporteuse1. La forme étant du au fait que nous utilisions pour le filtrage un cossinus surélevé.

  == Comparaison du TEB simulé avec le TEB théorique de la chaine étudiée

  #figure(
  image("Tracé1.4.png", width: 80%),
  caption: [
    TEB théorique et simulé 
  ])<TEBporteuse>

  Nous voyons que le TEB simulé est proche du TEB théorique, ce qui est une bonne nouvelle, celà signifie que notre chaine de transmission est bien implantée.

  Nous avons pour équation du TEB théorique : $Q(sqrt(2"E"_b/"N"_0))$

  = II : Implantation de la chaine passe-bas équivalente à la chaine de transmission sur porteuse précédente

  == Tracé des signaux générés sur les voies en phase et en quadrature et tracé du signal transmis

#figure(
  image("Tracé2.1.png", width: 80%),
  caption: [
    Tracé de la voie en phase avec 16 bits et un span de 4.
  ],
)<phase2>
#figure(
  image("Tracé2.2.png", width: 80%),
  caption: [
    Tracé de la voie en quadrature du signal avec 16 bits et un span de 4.
  ],
)<quadrature2>

On voit ici que les signaux ont une amplitude plus faible que sur la porteuse, celà est du au fait que nous sommes en bande de base, et que nous avons un filtrage passe-bas. De plus le span est toujours présent, d'où ce décallage encore présent.

== Tracé de la densité spectrale de puissance du signal transmis en bande de base.

#figure(
  image("Tracé2.3.png", width: 80%),
  caption: [
    Densité spectrale de puissance du signal transmis sur fréquence porteuse avec 10000 bits.
  ])<DSPporteuse2>

  Nous voyons maintenant que notre densité spectrale de puissance est centrée autour de 0, ce qui est normal, car nous sommes en bande de base. Nous voyons aussi que la forme est similaire à celle de la porteuse, dû au fait que nous utilisons un cossinus surélevé pour le filtrage.

  == Tracé des constellation pour des $E_b/N_0$ différents

  #figure(
    image("Tracé2.4.png", width: 80%),
    caption: [
      Constellation pour différents $E_b/N_0$
    ],
  )<constellation1>

  Nous voyons que pour un $E_b/N_0$ faible, les points sont très proches, et donc difficilement déchiffrable, alors que pour un $E_b/N_0$ élevé, les points sont bien espacés, et donc facilement déchiffrable. Plus le $E_b/N_0$ est élevé, plus la qualité de la transmission est bonne car nous aurons un TEB meilleur.

  == Comparaison du TEB sur porteuse avec le TEB en bande de base

  #figure(
    image("Tracé2.5.png", width: 80%),
    caption: [
      Comparaison du TEB sur porteuse avec le TEB en bande de base
    ],
  )<TEBporteuse2> 

  Nous voyons que l'éfficacité en puissance est meilleure pour la porteuse, ce qui montre que la transmission sur porteuse aura un meilleur TEB pour un même $E_b/N_0$. Mais la transmission en bande de base à une meilleure éfficacité spectrale, ce qui fait que nous aurions besoin d'une bande plus petite pour transmettre le même nombre de bits.

  = III : Comparaison du modulateur DVS-S avec un modulateur 4-ASK

  == Implantation de la modulation 4-ASK 

  === Tracé des constellation  pour différentes valeurs de $E_b$/$N_0$


  #figure(
    image("Tracé3.1.png", width: 80%),
    caption: [
      Constellation pour différents $E_b/N_0$
    ],
  )<constellation2>

  Nous voyons que pour un $E_b$/$N_0$ élevé, les répartitions du nombre d'occurences nous montre bien les différentes valeurs de la constellation. Alors que pour un $E_b$/$N_0$ faible, les points sont plus aléatoires, et donc le nombre d'occurences de nos valeurs sont beaucoups plus difficiles à distinguer.

  === Comparaison du TEB simulé avec le TEB théorique

  #figure(
    image("Tracé3.2.png", width: 80%),
    caption: [
      Comparaison du TEB simulé avec le TEB théorique
    ],
  )<TEBASK>

  Nous voyons que le TEB simulé est proche du TEB théorique, ce qui est une bonne nouvelle, celà signifie que notre chaine de transmission est bien implantée.

  Nous avons pour équation du TEB théorique : $3/4Q(sqrt(12/15"E"_b/"N"_0))$