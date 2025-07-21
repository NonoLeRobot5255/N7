#import "@preview/diagraph:0.3.2":raw-render
#import "@preview/fletcher:0.5.6"  as fletcher: diagram, node, edge
= Serveurs homogènes

#diagram(
  node-shape:rect,
  node-stroke:0.1em,

  node((0,0),$X$),
  node((0,-0.4),$mu$, stroke:0em),
  node((0,1),$X$),
  node((0,0.6),$mu$, stroke:0em),
  node((-1,0.5),$| |$),

  edge((-2,0.5),(-1,0.5),"-|>",$lambda$),
  edge((-1,0.5),(0,0)),
  edge((-1,0.5),(0,1)),
  edge((0,0),(1,0.5)),
  edge((0,1),(1,0.5)),
  edge((1,0.5),(2,0.5), "-|>")
  
)
+ Donner la notation de Kendall de cette file.
  - $M"/"M"/"2$
    
    $rho = lambda/(2 mu)$

    C'est moins bon qu'un seul serveur de taux de service $2 mu$ car le débit ici est soit 0 quand la file est vide, soit $mu$ quand 1 serveur est pris soit $2 mu$ quand les 2 serveurs sont pris. Alors qu'avec un seul serveur de taux de service $2 mu$, c'est soit 0, soit $2 mu$.
  
  _Hint: Comment montrer une CMTC: voir l'évolution du système, elle ne dépend que des instants passé, on peut le "deviner"
  ce qui fait evoluer le système: arrivées et départs._

+ On note $N(t)$ le nombre de clients dans la file à l'instant $t$.
  Montrer que ${N(t), t <= 0}$ est un processus markovien. de naissance et de mort.
  - Pour les arrivées, c'est trivial:
    - $PP(1 "arrivée entre" t "et" t + d t) = lambda dot d t + o(d t)$
    - $PP(0 "arrivée entre" t "et" t + d t) = 1 -lambda dot d t + o(d t)$
  - Pour les départ:
    - $PP(1 "service en cours à instant "t" se termine entre" t "et" t + d t) = mu dot d t + o(d t)$
    - $PP(1 "service en cours à instant "t" ne se termine pas entre" t "et" t + d t) = 1 - mu dot d t + o(d t)$
    - $PP(1 "départ entre" t "et" t + d t | N(t) = 0) = o(d t)$
    - $PP(1 "départ entre" t "et" t + d t | N(t) = 1) = mu d t + o(d t)$
    - $PP(0 "départ entre" t "et" t + d t | N(t) = 1) = 1 - mu d t + o(d t)$
    - $PP(1 "départ entre" t "et" t + d t | N(t) = k >= 2) = 2 mu d t + o(d t)$
    - $PP(0 "départ entre" t "et" t + d t | N(t) = k >= 2) = 1 - 2 mu d t + o(d t)$
    - CMTC de type processus de naissance et de mort 

  *graph De la CMTC*
      
  #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((0,0), $0$),
    node((1,0), $1$),
    node((2,0), $2$),
    node((3,0), $3$),
    node((4,0), $4$),
    node((5,0), $5$),
  
    edge((0,0),(1,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((1,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((2,0),(3,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((3,0),(4,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((4,0),(5,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    
    edge((1,0), (0,0),loop-angle : 30deg, bend : 30deg, "-|>", $mu$),
    edge((2,0), (1,0),loop-angle : 30deg, bend : 30deg, "-|>", $2  mu$),
    edge((3,0), (2,0),loop-angle : 30deg, bend : 30deg, "-|>", $2  mu$),
    edge((4,0), (3,0),loop-angle : 30deg, bend : 30deg, "-|>", $2 mu$),
    edge((5,0), (4,0),loop-angle : 30deg, bend : 30deg, "-|>", $2 mu$),
  )

+ On veut calculer les probabilités des divers états possibles. On note la probabilité qu'il y ait i clients dans la file à l'état stationnaire. Démontrer que pour , avec . Calculer. Quelle est la condition de stabilité de la file ?

  - Si la chaine est ergodique, toutes les coupes sont respectées:

  - On a:
    $cases(lambda Pi_0 = mu Pi_1, 
    lambda Pi_1 = 2 mu Pi_2,
    dots,
    lambda Pi_k = 2 mu Pi_(k+1))$

  Donc en isolant le terme $Pi_k$ de gauche, cela donne:

    $cases(Pi_0 = mu/lambda Pi_1, 
    Pi_1 = 2 mu/lambda Pi_2,
    dots,
    Pi_k = 2 mu/lambda Pi_(k+1))$

    Par récurrence, on a alors:

    $Pi_k = lambda/(2 mu) Pi_(k-1) = 2 rho^k Pi_0$
    
  Or: $sum_(k=0)^infinity Pi_k = 1$

  Donc en remplaçant, on a: $Pi_0 dot (1 + 2 rho + dots + 2 rho^k + dots) = 1$

  On remarque donc une série géométrique de premier terme $2 rho$ et de raison $rho$.

  Elle ne converge que si: $rho < 1$, si c'set le cas:
  
  $Pi_0 dot (1 + "série géométrique") = Pi_0 dot (1 + (2 dot rho)/(1 - rho)) = 1$

  donc *$ Pi_0 = (1- rho)/(1 + rho) $*

+  En généralisant pour les $Pi_k$ avec leurs expressions en foction de $Pi_0$:
$Pi_k = 2 rho^k dot (1- rho)/(1 + rho)$

$E(L) &= sum^infinity_(k=1) k dot Pi_k = sum^infinity_(k=1) k dot 2 dot rho^k dot (1- rho)/(1 + rho)\
&= 2 dot (1- rho)/(1 + rho) dot sum^infinity_(k=1) k dot rho^k = 2 dot (1- rho)/(1 + rho) dot rho/(1-rho)^2\
&= 2dot rho/(1-rho^2)$


$E(R) &= E(L)/Lambda = E(L)/lambda\
&= (2 dot lambda/(2mu)dot 1/lambda)/(1-rho^2) = 1/mu(1-rho^2)$



= Serveurs hétérogènes

#diagram(
  node-shape:rect,
  node-stroke:0.1em,

  node((0,0),$X$),
  node((0,-0.4),$2mu$, stroke:0em),
  node((0,1),$X$),
  node((0,0.6),$mu$, stroke:0em),
  node((-1,0.5),$| |$),

  edge((-2,0.5),(-1,0.5),"-|>",$lambda$),
  edge((-1,0.5),(0,0)),
  edge((-1,0.5),(0,1)),
  edge((0,0),(1,0.5)),
  edge((0,1),(1,0.5)),
  edge((1,0.5),(2,0.5), "-|>")
  
)

On suppose maintenant que le serveur 1 est deux fois plus rapide que le serveur 2. On note le taux de service du serveur 1 et le taux de service du serveur 2.

Le choix du serveur se fait de la façon suivante:
- Si un seul serveur est disponible, le premier client en attente choisit ce serveur
-  Si les deux serveurs sont libres, le premier client en attente choisit le serveur le plus rapide (le serveur 1).

+ On note N(t) le nombre de clients dans la file à l'instant t.
  N(t) est-il un processus markovien ?
  - Stable quand $lambda < 3 mu$ Pas égal car dans ce cas on se retrouve dans une chaine avec des états récurrents nuls.
  - Ce n'est pas une CMTC car l'état courant du système ne permets pas de voir le future du système: quand un paquet arrive, on sait pas s'il sera envoyé en haut ou en bas. Mais on peut tout de même écrire des éléments sur les probabilités:
  

  - Pour les arrivées, c'est trivial:
    - $PP(1 "arrivée entre" t "et" t + d t) = lambda dot d t + o(d t)$
    - $PP(0 "arrivée entre" t "et" t + d t) = 1 -lambda dot d t + o(d t)$
  - Pour les départ:
    - $PP(1 "départ entre" t "et" t + d t | N(t) = 0) = o(d t)$
    
    - $PP(1 "départ entre" t "et" t + d t | N(t) = 1) = "inconnu"$
      - *C'est lui qui fait que c'est pas une CMTC*
    
    - $PP(1 "départ entre" t "et" t + d t | N(t) = k >= 2) = 3 mu d t + o(d t)$
    - $PP(0 "départ entre" t "et" t + d t | N(t) = k >= 2) = 1 - 3 mu d t + o(d t)$
    
  *graph De la CMTC*

  #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((0,0), $0$),
    node((1,0), $1$),
    node((2,0), $2$),
    node((3,0), $3$),
    node((4,0), $4$),
    node((5,0), $5$),
  
    edge((0,0),(1,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((1,0),(2,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((2,0),(3,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((3,0),(4,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((4,0),(5,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    
    edge((1,0), (0,0),loop-angle : 30deg, bend : 30deg, "-|>", $?$),
    edge((2,0), (1,0),loop-angle : 30deg, bend : 30deg, "-|>", $3  mu$),
    edge((3,0), (2,0),loop-angle : 30deg, bend : 30deg, "-|>", $3  mu$),
    edge((4,0), (3,0),loop-angle : 30deg, bend : 30deg, "-|>", $3 mu$),
    edge((5,0), (4,0),loop-angle : 30deg, bend : 30deg, "-|>", $3 mu$),
  )

  
+ On va séparer l'état où l'on a un seul client dans la file en deux états:
  - état 1': il y a un seul client dans la file, il se trouve dans le serveur 1.
  - état 1": il y a un seul client dans la file, il se trouve dans le serveur 2.
    On considère le processus ${E(t), t>=0)$:

  E(t)=i, avec i=0 ou $i>=2$ s'il y a i clients dans la file à l'instant t
  - E(t)=1', s'il y a un client dans la file à l'instant t qui se trouve dans le serveur 1
  - E(t)=1", s'il y a un client dans la file à l'instant t qui se trouve dans le serveur 2
  Montrer que E(t) est un processus markovien.
  Calculer les taux d'arrivée et de départ conditionnels.
  E(t) est-il un processus de naissance et de mort ?

  - Etat 1':
    - $PP(1 "départ entre" t "et" t + d t | E(t) = 1') = 2 mu d t + o(d t)$
    - $PP(0 "départ entre" t "et" t + d t | E(t) = 1') =1 - 2 mu d t + o(d t)$
  - Etat 1'':
    - $PP(1 "départ entre" t "et" t + d t | E(t) = 1'') = mu d t + o(d t)$
    - $PP(1 "départ entre" t "et" t + d t | E(t) = 1'') = 1 - mu d t + o(d t)$

  
  #diagram(
    node-stroke : 0.1em,
    node-shape : circle,
  
    node((0,0), $0$),
    node((1,-1), $1'$),
    node((1,1), $1#text["]$),
    node((2,0), $2$),
    node((3,0), $3$),
    node((4,0), $dots$,stroke:0em),
    node((5,0), $k$),
    node((6,0), $dots$, stroke:0em),
  

    edge((2,0),(3,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((3,0),(4,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((4,0),(5,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    edge((5,0),(6,0),loop-angle : 30deg, bend : 30deg, "-|>", $lambda$),
    
    edge((1,-1),(2,0),loop-angle : 30deg, bend : 20deg, "-|>", $lambda$),
    edge((1,-1),(0,0),loop-angle : 30deg, bend : 20deg, "-|>", $2mu$),
    edge((2,0),(1,-1),loop-angle : 30deg, bend : 20deg, "-|>", $mu$),
    
    edge((1,1),(2,0),loop-angle : 30deg, bend : 20deg, "-|>", $lambda$),
    edge((2,0),(1,1),loop-angle : 30deg, bend : 20deg, "-|>", $2 mu$),

    edge((1,1),(0,0),loop-angle : 30deg, bend : 20deg, "-|>", $mu$),
    edge((0,0),(1,-1),loop-angle : 30deg, bend : 20deg, "-|>", $lambda$),

    
    edge((3,0), (2,0),loop-angle : 30deg, bend : 30deg, "-|>", $3  mu$),
    edge((4,0), (3,0),loop-angle : 30deg, bend : 30deg, "-|>", $3 mu$),
    edge((5,0), (4,0),loop-angle : 30deg, bend : 30deg, "-|>", $3 mu$),
    edge((6,0), (5,0),loop-angle : 30deg, bend : 30deg, "-|>", $3 mu$),
  )


  #text(["2"]) a trois voisins ; ce n'est pas un processus de naissance et de mort

  #grid(
    columns: 2, column-gutter: 10mm,
    [$lambda Pi_2 = 3mu Pi_3$\
    
    $lambda Pi_3 = 3 mu Pi_4$\
    #linebreak()
    $lambda Pi_k = 3 mu Pi_(k+1)$],
    [ $Pi_3 = lambda/(3 mu) Pi_2$\
    
  $Pi_4 = (lambda/(3 mu))^2 Pi_2\
  
  Pi_(k+2) = (lambda/(3 mu))^k Pi_2 "pour" k>=0$
  ]
    )
  
  De là on déduit les équations suivantes:
  
  $(C_0) " " lambda Pi_0 = 2mu Pi_(1') + mu Pi_(1'')$
  
  $(C_1) = (lambda + mu) Pi_(1'') = 2 mu Pi_2$
  
  $(C_2) lambda (Pi_1' + Pi_1'') = 3 mu Pi_2$

+  Avec *$lambda = mu$ d'après l'énoncé*, on déduit de $(C_1)$ que $Pi_(1'') = Pi_2$, de $(C_2)$ que $Pi_(1') = 2 Pi_3$ et on déduit après de $C_0$ que $P
  - $PP(1 "départ entre" t "et" t + d t | E(t) = 1') = 2 mu d t + o(d t)$i_0 = 5 Pi_2$

  
  
  
  $Pi_2(5+2+1+sum^infinity_(k=0)(1/3)^k) = 1\
  Pi_2 = 2/19\
  Pi_0 = 10/19, Pi_(1') 4/19 , Pi_(1'')= 2/19\
  Pi_(k+2) = (1/3)^k dot 2/19
  $

+ #v(1.5mm)
  $E(L) &= 0 dot Pi_0 + 1 dot Pi_(1') + 1 dot Pi_(1'') + 2 dot Pi_2 + 3dot Pi_3+ dots\
  &= 6/19 + 2/19sum^(+infinity)_(k=0) (k+2)(1/3)^k\
  &= 27/38\
  E(R) &= E(L)/lambda = 27/( 38lambda)$



  $U_1 = 1-Pi_0-Pi_(1'') = 7/19\
  U_2 = 1-Pi_0 - Pi_(1') = 5/19$


  *Temp moyen d'attente*

  $E(L_W)$ = nombre moyen de client en attente

  $E(W)$ = temps moyen d'attente

  - $E(L_w) &= sum_(k=2)^infinity (k-2)Pi_k\
  &= sum_(k=2)^infinity (k-2) dot (1/3)^k Pi_2 = 3/38$

  - $E(w) &= E(L_w)/lambda\
    &= 3/(38 lambda)$

  Et comme:
  
    $E(S) &= E(R) - E(w)\
    &= 27/(38 lambda) - 3/(38 lambda)\
    &= 12/(19 lambda)$

  $E(L_s_1) = U_1 dot 1 + (1- U_2) dot 0 = U_1$
  $E(L_s_2) = U_2 dot 1$

    

  Au vu des rapport comparé au taux de service total $3 mu$, on s'attendrait à ce que le serveur 1 ait une proportion de clients servis de $2/3$ et une proportion de $1/3$ pour le serveur 2.

  Or au vu de l'attribution quand ils ne sont pas remplis, les proportions réels sont:

  - On note $p$ la proportion de clients servis par le 1er serveur.
  - Donc $1-p$: proportion de clients servis par le 2e serveur.

  $E(S) = p E(S_1) + (1 - p) E(S_2)$

  On remplace avec les valeurs que l'on connait: $(E(S),E(S_1), E(S_2))$

  $12/(19 lambda) &= p/(2 mu) + (1-p)/mu \
12/19 &= 1 - p/2\
p/2 &= 7/19 => p = 14/19$
  
*Autre methode*

$E(L_S_1) = p dot lambda dot E(S_1)$

$17/19 = U_1 = p dot cancel(lambda)/(2 cancel(mu))$

Donc: *$ p = 14/19 $*