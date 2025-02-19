= CM de la matière réseau de mobiles

== Intro 
On parle de plusieurs choses : 
- Système 2G : GSM 
- Système 3G : UMTS et HSPA
- Système 4G : LTE

On dit réseaux de mobiles car c'est les utilisateurs qui bougent.

Plusieurs acteurs donc archi de communication complexe. (Pas comme réseau locaux)

GSM = remplacer paire torsadée par ondes radio + pouvoir être mobile. Apparition du sms par exemple mais plus de voix qu'autre choses.

Une génération de réseau = dure 10 ans.

3G car on fait plus d'autre chose que de la voix donc on a des besoins différents.

On transfère les données en mode paquet. On peut lisser la bande passante mais beaucoup de latence et gigue. 
Pour téléphonie on fait du mode circuit. On peu prendre que peu de bande passante mais pas beaucoup de latence et de gigue.

en 4G on a que des paquets. On utilise par exemple VOIP.

DVB = Digital Video Broadcasting
Pas grand intéret d'avoir une adresse IP fixe pour un mobile. On a une adresse IP dynamique. Sauf pour certains cas.

Réseaux de mobiles = réseaux de téléphonie mobiles. (Gestion du nomadisme).

Première solution : On donne une adresse temporaire si l'utilisateur est pas dans sa zone de couverture. Mais il garde quand même son adresse IP.

Milieu année 90 : 

Bibop = on doit être a cotés de la base pour que ça marche. Donc pas de mobilité.  

GSM = Découpement temporel du signal.

Besoin d'ordonnancement, on utilise une méthode d'accés de type polling (on demande à chaque utilisateur si il a des données à envoyer). Sauf que là c'est les utilisateurs qui envoie des demande de parole.

Transfert inter cellulaire = on doit changer de cellule. On doit changer de fréquence.
Problème de paging = on doit savoir où est l'utilisateur.


== GSM

On divisie les canaux en temps, et on alloue un slot sur 4 par exemple pour un utilisateur. Et on à un canal dédié pour la signalisation sauf que ça prend pas tant de ressources que ça et on à un débit constant "gaché".

On a des Comon Control chanel pour voir sir l'utisateur bouget et le changer de cellule ou pas en conséquance. dans le domaine des réseaux cellulaire c'est le réseau qui déclenche le changement de cellule. canal de paging pour localiser précisément l'utilisateur quand on a besoin de lui envoyer un message. on à aussi RACH pour demander un canal de parole (on utilise du haloa sloté avec une loi uniforme). BCH aussi pour du broadcast.

Sans connexion uniquement pour les remontées de mesure et pour et transfert inter cellulaire. Pour les doubles apppel on à plusieurs communication et un seul canal. 