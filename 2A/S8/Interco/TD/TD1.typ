= TD d'interconnexion 

== Exercice 1 : 

+ Qu'est ce qu'une archi de réseau
  - Description de l'ensemble des moyens pour faire communiquer des machines
  - Pas d'implémentation car laisse place à l'ingénieurie 
+ Quels sont les intérêts d'un modèle d'architecture de réseau hiérarchique
  -  ingénieurie = on divise le problème en sous-problèmes
  -  une couche n ne communique qu'avec la couche n+1 et n-1 sur une même machine, et n avec n sur des machines différentes
  -  Réponse : 
    -  Facilite l'évolution
    -  Mais on doit passer par toutes les couches pour communiquer (lenteur)
+ Qu'est ce qu'un protocole ? Qu'est ce qu'un service ? et un point d'accès  ?
  - Protocole : ensemble de règles pour communiquer, on doit spécifier tous les messages (Meilleur à définir par automate)
    -  Mais pas souvent prouvé (prouvé = automate) mais problème implantation et interpretation
  - service = ensemble de fonctions de la couche n à n+1
    - communiquer = envoie de données (data dans OSI)
    - service de mise en place de connexion = établir une connexion (connect dans OSI)
    - service de déconnexion = fermer une connexion (disconnect dans OSI)
    - 4 primitives :
        - Request 
        - Indication
        - Reponse
        - Confirmation
        - 4 pour connect et 2 pour les autres
    - _Avec ça on fait tout_
  
  - point d'accés au service = interface entre les couches (dans IP on appelle ça port) 
    - On peut les identifier de deux manières :
      - par un identifiant (numéro de port) (explicite)
      - Rien si (implicite) 

== Exercice 2 :

=== Mise en place de connexion 

+ On suppose tout d'abord que la couche (N-1) offre un service sans connexion et la couche (N) un service en mode connecté. 
  Décrire l'enchaînement des primitives de service de niveau (N) et (N-1) ainsi que l'envoi des PDU du niveau (N) et (N-1) 
  pour la mise en place d'une connexion de niveau N.

  - paramètre :
    - adresse de destionation 
    - Décrire la connexion 