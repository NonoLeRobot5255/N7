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
)<phase>
#figure(
  image("Tracé1.2.png", width: 80%),
  caption: [
    Tracé de la voie en quadrature du signal avec 16 bits et un span de 4.
  ],
)<quadrature>

On voit sur les deux illustrations, les bits transmis ont un retard du au span du cosinus surélevé. 
Nous voyons que l'amplitude entre les symboles reçu et transmis est différente, celà vient de la fréquence porteuse et du retour retour en bande de base. 

== Tracé de la densité spectrale de puissance du signal transmis sur fréquence porteuse.

#figure(
  image("Tracé1.3.png", width: 80%),
  caption: [
    Densité spectrale de puissance du signal transmis sur fréquence porteuse avec 10000 bits.
  ])<DSPporteuse>

  Nous pouvous voir deux pics, qui sont du au fait que nous passons sur porteuse, ce qui augmente la fréquence de notre densité spectrale de puissance initialement centré autour de 0, la densité spectrale de puissance étant symétrique, un deuxième pic apparait bien sur notre @DSPporteuse. La forme étant du au fait que nous utilisions pour le filtrage un cossinus surélevé.

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

  