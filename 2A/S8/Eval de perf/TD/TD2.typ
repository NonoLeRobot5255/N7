#import "@preview/diagraph:0.3.2":raw-render
#import "@preview/fletcher:0.5.6"  as fletcher: diagram, node, edge

= Performances de Réseaux

== #underline[Exercice n°1 : Modèle d’un réseau téléphonique avec répétitions d’appels]

Dans le modèle d’un lien d’un réseau téléphonique par une file d’attente de type , on suppose qu’un nombre
fini N d’utilisateurs se partagent un lien pouvant multiplexer C appels au maximum. Dans le cas où toutes les ressources sont
occupées, les demandes de communications qui échouent seront éventuellement renouvelées au bout d’une durée qui a la
même loi que la durée normale qu’un utilisateur prend entre la fin d’un appel téléphonique et la demande suivante.
Dans la pratique, les utilisateurs ont tendance à renouveler rapidement et un certain nombre de fois leur demande puis à se
décourager.
On se propose de modéliser ce comportement par le schéma de la figure 1.

- La file à C serveurs (file 1) modélise le lien
-  La file à (N - C) serveurs (file 2) représente les utilisateurs qui ont vu leur communication refusée et qui vont renouveler
  leur appel
-  La file à N serveurs (file 3) représente les abonnés en attente entre deux communications
- On a un réseau de files d’attente fermé avec N clients dans le réseau.


#figure(image("../CM/images/figure1.png"), caption: [Modèle d’un lien téléphonique, population limitée et répétition d’appels])


On fera les hypothèses de traffic suivantes : 
- La durée entre la fin d’une communication et la suivante suit une loi exponentielle de taux $lambda$ ;
- La durée d’une communication téléphonique suit une loi exponentielle de taux $mu$;
- La durée entre deux tentatives suit une loi exponentielle de taux $gamma$ (indépendant du rang de la tentative)
- La probabilité qu’un utilisateur renouvelle sa tentative vaut H > 0 (indépendant du rang de la tentative)



=== Etude du système

+ On note $N_i (t)$ le nombre de clients dans la file i à l’instant t. Montrer que le couple  ${N_1 (t),N_2 (t), t in RR)}$est un
  processus markovien dont on déterminera soigneusement l’espace d’états $Omega$ et les taux de transition.

  - On détermine le nombre de clients dans chaque file:
    - file 1: $in [0,CC]$
    - file 2: $in [0,NN-CC]$
    - file 3: on s'en fiche car si on connait file 1 et file 2, on peut en déduire la file 3:
      - $N_1(t) + N_(t) + N_3(t) = N$, on ne peut alors que considerer un état par le couple (file 1, file 2)






+ Cas particulier N=3 C=2

  #diagram(
  node-shape:rect,
  node-stroke:0.1em,

  node((4,0),$1$),
  node((-1,-0.4),$lambda$, stroke:0em),
  node((4,1),$2$),
  node((4,-0.5),$mu$, stroke:0em),
  node((-1,1.),$3$),
  node((-1,0.5),$2$),
  node((-1,0),$1$),
  node((2,1),$1$),
  node((2,0.6),$gamma$, stroke:0em),

  edge((-2,0.5),(-1,0.5),"-|>",$lambda$),
  
  edge((-0.5,0.5),(3.5,0.5), "-|>"),
  edge((3,0.5),(3,2),"-|>"),
  edge((5,0.5),(5,2),"-|>"),
  edge((5,2),(-2,2)),
  edge((-2,2),(-2,0.5),),
  edge((3,1),(2.5,1),"-|>"),
  edge((1.6,1),(1.4,1),"-|>"),
  edge((1.4,1),(1.4,0.5),"-|>"),
  
  
  
  )

  Afin de déterminer les taux des transitions:
  - Pour les départ de la file 1:
    - $PP(N_1(t+d t) = n_1 - 1, N_2(t + d t) = n_2 | N_3(t) = n_3 > 0, N_2(t) = n_2) = mu n_1 d t + o(d t) $ // Car taux de départ mu et il y a n_1 personnes
  -  Pour les départ de la file 2 soit il renouvelle (retour file 2), soit il abandonne (aller file 3):
    - $PP(N_1 (t+ d t) = n_1 +1, N_2 (t+d t) = n_2 -1 | N_1 (t) = n_1 << N_2 (t) = n_2 >0) = gamma m_2 d t + o(d t)$ 
    - Abandonne: $PP(N_1 (t+ d t) = c, N_2 (t+d t) = n_2 -1 | N_1(t) = c, N_2(t) = n_1 ) = gamma n_2 (1-H) d t + o(d t)$
  - Pour le départ de la file 3 :
    - $PP(N_1(t + d t) = n_1 +1, N_2(t + d t) = n_2 | N_1(t) = n_1 = c, N_2(t) = n_2) = (N - n_1 - n_2) lambda d t + o(d t)$
    - $PP(N_1(t + d t) = c, N_2(t + d t) = n_2 - 1 | N_1(t) = n_1 = c, N_2(t) = n_2 < N - c) = (N - C - n_2) lambda dot H d t + o(d t)$
    

  *explication de :*

 #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((0,0), $0, 0$),
    node((1,0), $1, 0$),

    edge((0,0),(1,0),loop-angle : 30deg, bend : 30deg, "-|>", $N lambda$),
    edge((1,0), (0,0),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),
  )

  Dans 0,0, il y a N clients dans la file 3, donc le taux de départ est $N lambda$.

 On en déduit que dans 1,0, le taux de départ est $(N-1) lambda$ car il n'y a alors que N-1 clients dans la file 3.

 Le taux d'arrivée de 0,0 depuis 1,0 est $mu$ car il n'y a qu'un client dans la file 1 à ce moment, qu'il y en a N-1 dans la file 3, et que $mu$ est le taux de départ de la file 1. 


 On fait le diagramme pour N = 3, C = 2, donc N-C = 1

 #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((1,0), $0, 0$),
    node((2,0), $1, 0$),
    node((3,0), $2, 0$),
    node((3,2), $2, 1$),
    node((2,2), $1, 1$),
    node((1,2), $0, 1$),

    

    edge((1,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $2 lambda$),
    edge((2,0), (1,0),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),
    edge((3,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),
    edge((2,0), (3,0),loop-angle : 30deg, bend : 30deg, "-|>", $ lambda$),
    edge((3,0), (3,2),loop-angle : 30deg, bend : 30deg, "-|>", $ H lambda$),
    edge((3,2),(3,0),loop-angle : 30deg, bend : 30deg, "-|>", $ gamma (1 - H)$),
    edge((3,2),(2,2),loop-angle : 30deg, bend : 30deg, "-|>", $ 2 mu$),
    edge((2,2), (3,2),loop-angle : 30deg, bend : 30deg, "-|>", $ lambda$),
    edge((1,2),(2,2),loop-angle : 30deg, bend : 30deg, "-|>", $  2 lambda$),
    edge((2,2), (1,2),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),

    edge((2,2),(3,0),loop-angle : 30deg, bend : -110deg, "-|>", $gamma$),
    
    edge((1,2),(2,0),loop-angle : 30deg, bend : 1deg, "-|>", $gamma$),
  ) 
  
  #v(10mm)
  $U = (sum^C_(N_1=0) sum_(N_2=0)^(N-C) n_1 dot Pi(n_1,n_2))/C $
  
  
  $Lambda_0$ trafic offert 
  
+ $Theta = X/Lambda_0 = 1 - Lambda/Lambda_0$
  
  $Lambda = sum_(n_1 = 0)^C sum_(n_2 = 0)^(N-C) n_1 mu Pi(n_1,n_2)$
  
  $Lambda_0 = sum_(n_1 = 0)^C sum_(n_2 = 0)^(N-C) (N-n_1-n_2) dot lambda dot Pi(n_1,n_2)  $
  

=== Etude de comportements limites du système

On a $gamma = lambda$

+ Comme les 2 files (2 et 3) ont le même comportement, on peut les fusionner et donc on a une chaine de Markov

  On calcule les taux de probabilité
  - $PP(N_1(t + d t) = n_1 - 1| N_1(t + d t) = n_1) = n_1 mu d t + o(d t))$
  - $PP(N_1(t + d t) = n_1 + 1 | N_1(t + d t) = n_1) = (N-n_1) lambda d t + o(d t)$
  
  On perds les probas H.


+
 #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((1,0), $0$),
    node((2,0), $1$),
    node((3,0), $...$),
    node((4,0), $C$),

    

    edge((1,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $N lambda$),
    edge((2,0), (1,0),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),
    edge((3,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $ 2mu$),
    edge((2,0), (3,0),loop-angle : 30deg, bend : 30deg, "-|>", $ (N-1) lambda$),
    edge((4,0),(3,0),loop-angle : 30deg, bend : 30deg, "-|>", $ C mu$),
    edge((3,0), (4,0),loop-angle : 30deg, bend : 30deg, "-|>", $ (N-C+1)lambda$),
  ) 

  C'est la même chose qu'une file M/M/C/C/N.

+

  On a $Pi_k = ((N/k) rho^k)/(sum^c_(j=0) (mat(N;j) dot rho^j)$
  
  Ainsi que: $U = (sum_(k = 0)^C k dot Pi_k)/C$




+ C'est le cas où l'utilisateur retente toujours de passer son appel (H=1)

  C'est le cas optimal car comme $1/gamma -> 0, gamma -> infinity$, ce qui corresponds au fait que dès que qqun quitte la file (appel passé ou refusé), il y a automatiquement quelqu'un d'autre qui arrive.


2.4: C'est l'équivalent d'une chaine M/M/C/N/N


$ U = 1/C dot {sum_(k=0)^C k dot Pi_k + C sum_(k=c+1)^N dot Pi_k} $


4.1: La chaine est maintenant:M/M/N/N/N, c'est la situation où il y a autant d'utilisateur que de serveurs.


$C(v) = sum_ (s!=v,t!=v) ( sigma_(s,t) (v))/sigma_(s,t) $

 #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((1,0), $0$),
    node((2,0), $1$),
    node((3,0), $...$, stroke:0em),
    node((4,0), $N$),

    

    edge((1,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $N lambda$),
    edge((2,0), (1,0),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),
    edge((3,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $ 2mu$),
    edge((2,0), (3,0),loop-angle : 30deg, bend : 30deg, "-|>", $ (N-1) lambda$),
    edge((4,0),(3,0),loop-angle : 30deg, bend : 30deg, "-|>", $ N mu$),
    edge((3,0), (4,0),loop-angle : 30deg, bend : 30deg, "-|>", $ lambda$),
  ) 



4.2.

Il y a N serveurs et N clients, donc il y aura toujours un spot dispo. 

Pour 1 utilisateur:
Il utilisera soit 0, soit 1 ressource, qui est alors une chaine de Markov à 2 états:

 #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((1,0), $0$),
    node((2,0), $1$),

    

    edge((1,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((2,0), (1,0),loop-angle : 30deg, bend : 30deg, "-|>", $ mu$),

  )

$lambda Pi_0 = mu Pi_1$

$Pi_0 + Pi_1 = 1$

Donc:

$Pi_1 = lambda/(lambda +mu)  #h(15mm) (Pi_0 = mu/(lambda+mu)) $

$U = (N dot lambda/(lambda+ mu))/N = lambda/(lambda +mu) $






= Exercice 2: Longueur des paquets IP


+ Notation de Kendall

  Arrivée poissonnienne donc M, 1 seul serveur/file d'attente donc 1 et pour le service, comme cela dépends de la taille du paquet, c'est pas constant ni poissonnien, donc c'est quelconque (G)
  

    M/G/1

+ Déterminer le temps moyen passé par un paquet de chacun des trois types dans la file de sortie du routeur (attente + émission).
  - Les temps de réponse de chaque type de paquet va changer en fonction de sa taille ;
  - Le temps d'attente dans la file d'attente ne dépends pas de sa taille (car une seule file en FIFO). (n'est pas forcément le cas pour tout, mais quand c'est poissonnien, c'est sûr).

  $E(R_i) = E(S_i) + E(W)$
  
  $E(W) =^("Formume de Plachenkin?") (lambda dot (E(S^2)))/(2 dot (1 - rho))$

  $E(S) = E(p)/D$ (taille divisée par débit)

  $E(S^2) &= E(P^2)/D^2\
  &= ()"Var"(P) + E(P)^2)/D^2
  &= (sigma(P^2) + E(P)^2)/D^2$


  $rho &= lambda E(S)\
  &= lambda E(P)/D$

  $=> lambda = (rho D)/E(P)$


  Donc: $E(W) = (rho dot (sigma^2(P) + E(P)^2))/(2 dot D dot E(P)(1-rho))$

  $E(R_i) = l_i/D +E(W)$



+ Application numérique: On passe à 500 Gbs

  $E(R_i) = l_i/D +(0.8 dot (500^2 + 500^2))/(2 dot 10^10 dot 500(1-0.8))$

  $E(S_1) = 50*8/(100 dot 10^9) = 4$ms

  $E(S_1) = 500*8/(100 dot 10^9) = 40$ms

  $E(S_1) = 1500*8/(100 dot 10^9) = 120$ms
  
  $E(w) &= (4 * 0.8((500*8)^2 + (500 * 8) ^2))/(2 * 100 * 10^9 * (500*8) (1-0.8))\
  &= (2*2(500*8)^2)/((500*8)*100*10^9) = 160*10^(-9) = 160 m s$  


  $E(R_1) = 164"ms"$

  $E(R_2) = 200"ms"$

  $E(R_3) = 280"ms"$

== Point bonus:

  Si l'arrivée est "constante" ces résultats dépendraient de l'ordre d'arrivée: (les $l_1$ peuvent passer de 0 attente à très long en fonction de s'ils arrivent avant ou après les plus gros, ainsi que la durée entre l'arrivée des paquets)
  
#pagebreak()


= Poubelle
hello darkness my old friend...

hellhuile
...
#emoji.oil

*_coucou je suis nolann_*