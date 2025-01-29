= CM d'interconnexion 

== Premier CM 

Dans ce premier CM, on à vu des généralités sur l'interconnexion de réseaux, surtout le modèle OSI et les normes ISO dedans (en anglais c'est l'inverse).

== Deuxième CM et,plus

En dessous de la couche transport $->$ tout va bien mais au dessus de la couche transport $->$ tout va mal.
Standard aussi met en place standard sur métric et sur les délai $->$ usine à gaz infâme.
=== TCP
TCP = fiabilité (sans contrainte sur le délai)

Couche transport (IP) = on sait pas le chemin et en plus variance de temps sur le même chemin.

Plusieurs chemin avec des caractéristiques différentes et qui évolue dans le temps. Donc couche de transport doit regarder le chemin le plus avantageux.

Protocole = prouver formellement (protocole 0 de OSI)

=== UDP

UDP =  pas fiable mais très rapide.

Couche Session = point de synchronisation a différents poinrs du transfert pour savuvegarder le temps de transfert (mais pas implanté dans OSI,laissé aux applications).

Couche présentation = se comprendre entre les pc (par exemple le codage des entier sur 4 bits ou 8 bits) mais aussi codage sans perte, chifrement. Mais pas implanté aussi.

Donc on passe de 7 à 5 couches.

couche appli = déjà pré coder de base et on spécifie juste (Un trucs bien dans le modèle OSI de base).

1 service = 1 ou plusieurs protocoles. 

Protocole priopriaitaire = danger car si on veut implanter un trucs on est obligé d'utiliser les machines de la même marque.

Protocole de routage = envoie d'info sur les routeurs pour savoir comment envoyer les paquets. Donc c'est applicatif $!=$ algorithme de routage.

ejac de caractéristiques = on peut pas tout faire en même temps. base de donnée = pas de perte de donnée, mais pas de rapidité.v  -->  (Merci Benjamin)

Problème des réseau locaux = partage de ressources (beaucoup de collision possible) $->$ Objectif des standars = éviter les collisions.

MAC = couche liaison de données + couche physique un peu. Car par exemple CDMA = écouter le support.


=== Monde des réseau de Télécom 

- Besoin de circuit 
- mais besoin de différents choses, donc plusieurs piles protocolaires(par exemple pendant l'appel pas de délai mais à l'établissement de l'appel pas besoin de gigue nul)

Si on sait pas comment on appel une unité de donnée, on l'appel un ...PDU (par exemple PHY-PDU, MAC-PDU, etc).

Différence entre routage et commutation =  en routage on établi un chemin, en commitation on dirige de l'entrée vers la sortie.

_Si tout était conforme au modèle aussi on aurait pas de gros problèmes d'interco_

=== Interconnexion 

On regarde où ça diverge et on met une passerelle entre ces deux endroits (dans le modèle OSI).

Problème, connecté vs non connecté.

- Non connecté avec non connecté = Simple
- Connecté avec connecté = un peu plus complexe
- Connecté avec non connecté = complexe
- Non connecté avec connecté = très complexe

Si on a deux vision de QOS, on discut ou OSEF ? 
Si on veux une garantie de service ?
Notion de débit ?

Le plus souvent on fait rien.


+ Exemple 1 : réseau téléphonique 

    - Interconnexion par traduction au niveau applicatif

+ Exemple 2 : X.25 sur frame relay
  
    - interco par encapsulation 
    - dans framerelay on a des tuyaux permanent
    - C'est très fiable mais on tombe en panne beaucoup.
+ X.25 sur TCP 
    - On utilise TCP pour X.25
    - On fait le contrôle de congestion plus bas que TCP car contrôle de congestion chez TCP.
    - On met un protocole entre X.25 et TCP, c'est le protocole XOT. De niveau 5 (applicatif) et X.25 est de niveau 3 (réseau).
    - Problème : 
        - fiabilité = OK
        - Adressage = on a juste une table de correspondance.
        - numéro de connexion = gérer  l'adressage


== Troisième CM
On lit le numéro de téléphone du destinataire et on sait la destination.
Ce qui va compter dans la QOS c'est le temps de propagation.

HDLC = avoir vie dure.

Q.931 = protocole de signalisation pour établir une connexion. (applicatif)

Q.921 = protocole de liaison de données (couche 2)

Si GSM alors Q.931 mais on doit faire une passerelle pour passer dans le réseau.

=== Voix sur IP

on envoie la parole dans les paquets IP. Mais on a des problèmes de délai et de gigue. car TCP pas fait pour ça.

comment on attape de la gigues ? On met des buffers en gros (on garde des paquets et on les lit en même temps).
pour les signalisations on utilise TCP ou UDP.

_Les opérateurs Télécom seront content quand la téléphonie sera morte_ (Car deux réseaux à opérer)

multicast = trouver un arbre de diffusion optimal mais c'est chiant.

On met une estampille temporelle dans les paquets pour savoir quand on les a reçu et avoir une idée du délai.

j'abandonne ici, ça va trop vite et le prof à dit je cite "_J'ai plus de temps je vais accélérer_" 