#import "../../../../template/template_2A.typ": *

#show: project.with(
  
  title: "Rapport du bureau d'étude sur l'OFDM",
  authors: (
    "MARTIN Nolann", ),
  teachers: (
    "BOUCHERET Marie-Laure", 
  ),
  year : "2024-2025",
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

  == Implantation sans intervalle de garde

  