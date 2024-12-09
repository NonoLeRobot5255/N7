#import "../../../../template/template_2A.typ": *

#show: project.with(
  
  title: "Rapport du bureau d'étude sur l'OFDM",
  authors: (
    "MARTIN Nolann", ),
  teachers: (
    "BOUCHERET Marie-Laure", 
  ),
  year : "2024-2025",
  profondeur : 2,
)


= Intro 

Le but de ce projet est de réaliser une étude sur l'OFDM (Orthogonal Frequency Division Multiplexing) et de mettre en place un système de communication numérique basé sur cette technologie.

Nous serons dans un contexte de canal sélectif en fréquence et nous serons la plupart du temps sur un canal sans bruit et sur un mapping BPSK, sauf sur la dérnière partie où nous étudierons l'impact du bruit sur la transmission avec une modulation QPSK.

= Implantation de la chaine de transmission OFDM sans canal

Dans cette partie nous implentons Une chaine de transmission OFDM sans canal. Pour étudier le comportement nous n'activeront que certaines porteuses. Nous distingueront 3 cas :

== Emission

=== Premier cas : 1 porteuse active 

#figure(
  image("../screen_rapport/porteuse 1 active.png",width: 80%), 
  caption: [Porteuse 1 active seulement]
  )

#figure(
  image("../screen_rapport/porteuse 4 active.png",width: 80%), 
  caption: [Porteuse 4 active seulement]
  )

Nous voyons que la porteuse active créer un "pic" sur notre DSP, ce qui est normal car nous avons une fréquence porteuse qui est active.
#pagebreak()
=== Deuxième cas : 2 porteuses actives.

#figure(
  image("../screen_rapport/porteuse 1 et 3 actives.png",width: 80%), 
  caption: [Porteuse 1 et 3 actives ]
  )

#figure(
  image("../screen_rapport/porteuse 4 et 5 actives.png",width: 80%), 
  caption: [Porteuse 4 et 5 actives]
  )

Nous voyons que les deux porteuses actives créent un "pic" sur notre DSP, le placement des pics étant déterminé par le nombre et le placement des porteuses actives. De plus on peut voir que si les deux porteuses sont côte à côte, les "pics" se rejoignent pour former un seul "pic".

=== troisème cas : 8 porteuses du milieu actives

#figure(
  image("../screen_rapport/8porteusesdumilieu.png",width: 80%), 
  caption: [Porteuse])


Nous voyons que les 8 porteuses du milieu étant actives, elles créent une sorte de palier du au fait qu'elles sont actives et que les autres porteuses sont inactives.

=== explication 

Nous avons parler de pics et de palier, ce qui se cache dans ces termes est le fait que la densité spéctrale de puissance est plus élevée à ces endroits là. Cela est du au fait que les porteuses actives vont créer des "pics" de puissance à ces endroits là. D'où le terme de pic.

== Réception sans canal

Dans cette partie nous vérifions qu'à la récéption notre TEB(Taux d'Erreur Binaire) sera nul. Pour cela les 16 porteuses seront actives. 

#figure(
  image("../screen_rapport/TEB+toutes_actives.png",width: 80%), 
  caption: [DSP des 16 porteuses actives et TEB]
  )

Nous vérifions bien que notre TEB est nul, ce qui est normal car nous n'avons pas de canal et que les 16 porteuses sont actives.

= Implantation de la chaine de transmission OFDM avec canal multi-trajets, sans bruit

Dans cette partie nous étudierons l'impact d'un canal sans bruit dont le canal multi-trajet est de la forme suivante :

$y(t)= 0.407x(t) + 0.815x(t - "Ts" ) + 0.407x(t - 2"Ts" )$

== Implantation sans intervalle de garde

Nous pouvons voir que en ayant ce filtre la réponse impulsionelle de notre filtre sera de la forme suivante :

$h (t) = 0,404delta(t) + 0,815delta(t-"Ts") + 0,407delta(t-2"Ts")$

Nous pouvons a présent tracer le module et la phase en fréquence du canal de propagation : 

#figure(
  image("../screen_rapport/phase et frequence.png",width: 80%), 
  caption: [Module et phase du canal de propagation]
  )

Nous pouvons voir à partir de ces figures qu'il y a une aténuration du signal sur la porteuse 8.

Ainsi nous pouvons observer l'effet qu'à ce canal sur notre densité spéctrale de puissance :

#figure(
  image("../screen_rapport/dsp canal.png",width: 80%), 
  caption: [densité spéctrale de puissance en sortie du canal]
  )

Nous pouvons constater que le canal a un effet sur notre DSP. En effet, la porteuse 8 est atténuée, ce qui correspond bien à nos attentes. En OFDM, nous utilisons un rectangle pour la mise en forme des symboles. Lorsqu’il traverse le canal de propagation, notre signal subit la réponse en fréquence de ce dernier, ce qui modifie sa mise en forme et entraîne l’atténuation observée.

Les constellations des symboles reçus peuvent être intéressantes à observés, nous pouvons donc tracer les constellations des porteuses 6 et 15 :

#figure(
  image("../screen_rapport/const 6 et 15.png",width: 80%), 
  caption: [constellation de la porteuse 6 et 15]
  )

Nous pouvons voir que la constellation de la porteuse 6 est déformée, ce qui est normal car elle est atténuée. La constellation de la porteuse 15 est quant à elle inchangée ou casiment. Nous voyons d'ailleurs une rotation induite par le canal.

Malheuresement, pour notre TEB, il n'est plus nul dans ce cas là, nous avons par exemple sur cette simulation un TEB de 0.3609, nous voyons ça car même si nous n'avons pas de bruit, le canal créer de l'intérference inter porteuses (ICI) en rompant l'orthogonalité et donc nous voyons aparaitre un $"TEB" > 0$.

== Implantation avec intervalle de garde composé de zéros

Dans cette partie, nous allons ajouter un intervalle de garde composé de zéros devant chaque symbole
OFDM transmis avant passage dans le canal de propagation.


