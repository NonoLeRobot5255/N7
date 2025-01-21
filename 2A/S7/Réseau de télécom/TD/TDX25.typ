= TD2: Circuit virtuel

== Partie 1: Etablissement de circuit virtuel

+ 
  Quel est la différence entre un circuit et un circuit virtuel ?

  Cicuit =  réserver ressources tout le long du trajet.

  Circuit virtuel = circuit établi mais aucune garantie de réservation de ressources.

  X25 = circuit virtuel mis en places entre les commutateurs de racordement entre deux terminaux.
  On ne refuse la connexion si le circuit est chargé a 70-80%.
+ Quels sont les messages qui permettant la mise en place du circuit virtuel ?

  DA = Demande d'appel

  Au moment de la connection que fais le commutateur/routeur ?

  + Vérifie si un chemin existe
  + Vérifie si il peut allouer de la ressource
  + Attribut un numéro de circuit

  On part sur les hypothèses suivantes quant à la disponibilité des voies logiques :
  - A ne parle pas encore avec son CA ;
  - CA et C1 ont de disponibles 1,4 et 7 ;
  - C1 et C2 4 ;
  - C2 et C3 5 et 8 ;
  - C3 et CB 1 et 2 ;
  - CB et B de 1 à 5.
  Représenter la mise en place du circuit virtuel.

  DA(A,B) --> 1 pour A,CA

  DA(A,B) --> 1 pour CA,C1

  DA(A,B) --> 4 pour C1,C2

  DA(A,B) --> 5 pour C2,C3

  DA(A,B) --> 1 pour C3,CB

  DA(A,B) --> 1 pour CB,B

  CA dans l'autre sens. pour confirmer la connection.

+ Dans X25 peut on réserver toutes les ressources du réseau ?
  
  Non, on ne peut pas réserver toutes les ressources du réseau car si on réserve tout et que tout le monde envoie un message en même temps, on ne pourra pas traiter les messages.

  Supposons alors que C2 ne dispose pas d’assez de ressources pour l’ouverture du CV. Que se
  passe t’il et quelle est signalisation mise en œuvre ?

  C2 envoie un D vers A.

  
== Partie 2 : Echange de données
#pagebreak()
+ #linebreak()
  
  #table(columns: 2,
  [DATA],[SIGNAL],
  [$T_"eA" = "taille"/"débit" = 1000/500 = 2s$],[0,2s],
  [$T_"eB" = 10s$],[1s],
  [$T_"ec-c" = 1s$],[0,1s])

  #figure(image("chronograme.drawio.png"))
  remarque : si il y a congestion ça sera sur CB,B
+ Réalisez le chronogramme le chronogramme de cette communication avec un mode de reprise
d’erreur de proche en proche.
  
  la même chose sauf que accusé de réception pas de bout en bout mais de proche en proche, donc congestion sur CB.

== Partie 3: Niveau 3 et Niveau 2

#figure(image("chronogramme fou.png"))