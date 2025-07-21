#import "@preview/diagraph:0.3.2":raw-render
#import "@preview/fletcher:0.5.6"  as fletcher: diagram, node, edge


= Controle de flux et réeaux de files d'attente

+ Est-on dans les conditions d'application du théorème de Jackson? Gordon et Newell?


  - Le théorème de Gordon Newell s'applique pour les réseaux de Jackson fermés, et ici on a un réseau ouvert. Ce théorème ne s'applique donc pas.
  -Pour Jackson on a:
    - 1 serv par file
    - File WAIT n'as pas de temps de service suivant une loi exponentielle, donc
  Donc on peut pas appliquer le théorème de Jackson.


+ On envisage un modèle ouvert approché dans lequel on suppose que les arrivées dans le réseau sont poissonniennes de taux $lambda$. (aka On vire la file WAIT). Quelles conditions de trafic peuvent rendre ce modèle raisonnable ? Dans ce cas quel théorème peut-on utiliser pour déterminer les performances du système ? Quel sera le temps moyen entre l'émission d'un paquet et la réception de son acquittement ?


  C'est comme si la file WAIT est presque tout le temps vide, donc il faut qu'il y ait toujours moins de N paquets dans file1/file2. Donc il faut que $lambda<<mu$ (partent plus vite qu'ils n'arrivent).

  On est donc dans les conditions d'application du théorème de Jackson (ouvert, et toutes files avec arrivée exponentielle).
  
  On l'applique pour dire que $rho_j = lambda_c_j/mu_j$.


  $q_0 = (1 #h(3mm) 0)$

  $P =mat(0,1;0,0)$ 

  $e_1 = 1$

  $e_2 = e_1 = 1$

  $rho = lambda/mu$

  $E(L_1) = rho_1/(1-rho_1) = lambda/mu/(1 - lambda/mu) $

  $E(L_2)= (lambda/mu)/(1-lambda/mu)$

  $E(L) = 2 dot rho/(1 - rho)$

  $E(R_1) = E(L_1)/lambda = 1/(1-mu)$

  $E(R_2) = 1/(mu - lambda)$

  $E(R) = E(L)/lambda = 2/(mu - lambda)$

  $E(R) = e_1 E(R_1) + e_2 E(R_2) = E(R_1) + E(R_2)$




+ On envisage un modèle fermé dans lequel on a en permanence N clients. (File wait n'est presque jamais vide). Le réseau est alors fermé.

  La condition est: $lambda ~ mu$. #h(5mm) $lambda > mu$ n'a pas réellement d'interet.

  On peut donc utiliser le théorème de Gordon Newell.

  Le débit est la valeur qui nous interesse ici. Le débit est majoré par $mu$.

  Il y a 2 points d'observations qui sont relativement identiques.

  On place le point d'observation avant la file 1.

  le système linéaire nous donne: $e = e dot P$

  $P = mat(0,1;1,0)$

  $e_1 = e_2$ #h(5mm) $e_2 = e_1$ Don on en vire une des 2.

  $e_1^* = 1 => e_2^* = 1$

  $Pi(N, 0) = G dot (e_1^"*"/mu)^N (e_2^"*"/mu)^0 =G(1/mu)^N = 1/(N+1)\
  Pi(N-1, 1) =G dot (e_1^"*"/mu)^(N-1) (e_2^"*"/mu)^1 =G(1/mu)^N = 1/(N+1)\
  .\
  .\
  .\
  Pi(0, N) = G dot (e_1^"*"/mu)^0 (e_2^"*"/mu)^N =G(1/mu)^N = 1/(N+1)$

  $U_1 &= 1 - Pi(0,N) = N/(N+1)\
  &= Lambda_1 E(S_1)\
  &= Lambda^"*" e_1^"*" E(S_1)\
  &= Lambda^"*"/mu$

  Avec: $Lambda^"*" = U_1 dot mu = (N mu)/(N+1)$

  $overline(R)^* = N/Lambda^* = N/(N mu)/(N+1) = (N+1)/mu$

  


