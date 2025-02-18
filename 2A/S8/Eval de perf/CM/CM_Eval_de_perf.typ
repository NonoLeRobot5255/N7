= CM de la matière évaluation de perfomances par André Luc Beylot

Réseau = ensemble de ccomposants dont on veut connaitre :
- perf individuelles
- perf globales

On supose en 1A que la proba de perte pour un routeur est indépendante de celle des autres routeurs. Mais en réalité, les pannes sont souvent corrélées. Car congestion, etc... Donc perf gloable = très compliqué.

Problème de deux types : 

- taille du réseau : plus il est grand, plus il est difficile de le modéliser
- temps : plus le temps passe, plus les pannes se produisent, plus le réseau est difficile à modéliser

On va parler en cours plus sur perf individuelles que globales. Mais TP = aussi sur perf globales.

== Réseau locaux
Pour réseau locaux : Problème = problème de collision (méthode d'accés) 

On a prouvé pour Haloa (0.18 ou 0.36) simplement.

Pour les autres c'est plus compliqué.


== Réseaux longue distance 

On étudie perte de paquets 

== Pour réseau de Télécoms

On étudie les circuits donc on étudie les blocages de créations de circuits. Et aussi problème de panne. 

On précalcule des chemins de secours.

== Réseau a commutation de paquets

Dans le réseau sémaphore, on fait de la commutation de message, on ne découpe pas en paquets. Car c'est des messages courts donc pas besoin de les découper. On fait du multiplexage statistique. 

On à une attente variable (aléatoire) pour les messages. Et on a une grosse perte de paquet pour deux raisons:

- File d'attentes qui se remplissent
- Pannes

Avant on faisait un accusé d'envoie de message possible sur le commutateur suivant. Mais très peu d'utilisation du réseau ($~$5%).

Dans le mode datagramme on envoie le problème aux extrémités. CF TCP qui gère les pertes et la congestion.

Dans les files d'attente pas la même chose entre pasuet et bits :

Paquet = un volume de bits qui peut être variable. Ex : Beaucoup de paquets de signalisation (accusé de réception) dans le sens montant.
bits = unité de donnée.

Circuit = suplanté par mode paquet car on à des besoins différents sur notre réseau.

On peut mettre de la Qos sur le réseau d'accés mais pas sur internet car plus petit et donc on connait le réseau (3 bonds environ). 
Si on veut une QoS de bout en bout on fait de la résérvation de ressources.

== ADSL 

Problème d'accés, on doit prednre des times slots pour pouvoir se connecter, et on prend un moment au hasard dans ce time slot.

== Méthodologie 

Dimensionnement de nouveaux systèmes

Optimisation de systèmes existants

Outils : 
- Modèle stochastique (probabiliste) pour l'irrégularité de l'utilisation du réseau

Formalisme :
- Files d'attente
- Automates (qualitatif) 
  - _Pour celui qui possède un marteau, tous les problèmes ressemblent à un clou_ (parlant des gens du labo Laplaces)
- Chaînes de Markov 

== Critères de performances

Temps de réponse :
- temps entre l'envoie de la req et le récép de la réponse
- Temps pour aller d'un bout à l'autre 

Débit = nomnbre d'entités par unité de temps

Utilisation des ressources = probabilité qu'une machine soit occupée 

...

== Modélisation

Modèle = représentation abstraite de la réalité (système physique à étudier)

Modélisation = Etape permettant de mettre en oeuvre un modèle

#h(5mm) - dépend des critères de performances voulues

#h(5mm)  - Impossbile de réprésenter le système complétement.

== Étude du modèle 

- Résolution analytique :
  - exactes 
  - approximatives

- Simu sur ordi 
- Mesures
  - active (on injecte directement du trafic et on regarde)
  - passive (on regarde ce qui se passe avec des mouchards)
- Combinaison de tout ça

== Méthode générale

_je mettrais un screen parce que flemme (slide 13)_