= intro

mom = message orientied model 

appel assynchrone des messages 

on s'intérèsse a la communicatiion sans qu'il y est de synchro (ex: mail où le pc à pas besoin d'être allumé pour recevoir le mail)

on cherche à implenter différenetes carréctéristiques de la communication mom : 

- assynchrone

- Anonyme (on ne sais pas à qui on envoie le message)

- $N-1$

== Message based middleware (principe) :

- message passing (envoie de message)

 -- très classique (socket)

- message queue (communicatiion avec une file d'attente perssisante)

 -- on rajoute la persistance (on peut envoyer un message même si le destinataire est pas là)

- model publish/suscribe 

 -- un producteur envoie un message à un topic et les consommateurs abonnés à ce topic recoivent le message

 -- on peut aussi faire avec des filtres (ex: je veux que les messages qui ont un certain mot), mais complexe +++
 

=== implémentation :

- Centralisé (Hub and spoke)

- Distribué (snow flake)

- software bus (bus de serveur)

== JMS (Java Message Service) :

- API pour la communication mom

implémente : 

- Message queue

- Publish/subscribe

- Event

À de nombreux avantages (portabilité etc...)
mais on ne peut pas faire avec plusieurs en même temps (utiliser celui d'IBM et oracle en même temps)