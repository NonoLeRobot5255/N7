
#import "template.typ": *
#import "@preview/diagraph:0.3.2":raw-render
#import "@preview/fletcher:0.5.6"  as fletcher: diagram, node, edge

#import "@preview/algorithmic:0.1.0"
#import algorithmic: algorithm

#import "@preview/lovelace:0.3.0": *


#show: project.with(
  title :  "Evaluation de performance",
  generalites: ("8 CMs ;","3 TDs ;","1 prépa de TP ;"," 7/8 TPs ;","Tous documents autorisés pour l'examen ;","Examen plus orienté utilisation d'outils qu'orienté maths."),
  definition:("Processus stochastique", "S","CMTD","Chaine de Markov à Temps Discret","fortement connexe","il existe un chemin d'un point A à un point B","ergodique","Relatif à un processus stochastique dont les statistiques peuvent être approchées par la connaissance d'une seule de ses réalisations","PASTA","Poisson Arrivals See Time Averages"),
)
//#raw-render(```dot
//digraph {
//  Zgeg [color=green]
//Zob -> Zgeg
//Zob -> caca
//caca -> Zgeg
//}
//```)
= Introduction (18/02/25)

Réseaux de communication est ensemble composants dont on veut connaître les performances indiv et globale.  Obj atteindre QoS attendu.

Pour globale juste généralisation, on prend les performances indiv et on multiplie ? V/F souvent F. Il faut que les compo soit indep et c'est faux. => compliqué

Echelle de tps ? pour bout en bout

Voir quoi retenir perf indiv et voir que qu'on peut se retrouver pour globale

- Qualitatif : protocole correct et correctement implémenter. Outils mathématiques automates... (parcours symbiot)
- Quantitatif : delai moy, taux de perte, gigue... Tout ce qui est quantifiable. outils math : probas, stats, algèbre
-> 2 mondes séparer. On va voir le côté quantitatif.

Chaque fam réseaux a ses pbl :
- rezo loco : méthode d'accès
- rezo longue distance : perte de paquet, controle flux/erreur, retransmission
- rezo telecom : ???

== rezo commutation de circuit
Les pbls de ces rezo c'est les pannes (e.g. coup de pelleteuse dans les câbles)
=> réseaux maillé pour solution secours si panne

*Proba quel nombre appels refusé pour eval perf.*

exemple:
2 commutateurs reliés par un lien. Déterminer proba qu'1 appel refusé car pas de place pour un lien.
Etudier avec un autre lien.

== rezo commutation de paquet
circuit virtuel et datagramme

rezo semaphore : datagramme en mode commutation de message -> pas de séquencement, fonctionne pour messages cours

multiplexage statistique

esperer debit fil d'attente baisse pour vider file d'attente

pbl : état fil d'attente

->  attente variable dependant de l'état d'engorgement quand paquet entre file d'attente => perte

*epee de damocles qui est qu'à des moments c'est engorgé*

necessiter implementer mecanisme de reprise (si on veut) (circuit virtuel).
pour datatgrame on envoie les pbl aux extrémitées.

*Problème théorie des files d'attentes.*

type longueur paquets:
- données : 1500 o
- signalisation : ack...

pbl pour sens communication. Sens montant bcp ack donc pourrir buffer avec bc de petits paquets

== Evolution des réseaux
mode circuit remplacé par mode paquet

QoS différentiée : plus facile reseaux acces qu'internet car plus petit qu'internet, la topologie est connue

== couche MAC
stations homologue/homogène : pas de connections
comment avoir commun ? :
- polling (70's) 
- méthode d'accès de type décentralisées sans collision (e.g. token ring, token bus, FDDI (jeton temporisé)) 
- méthode d'accès avec accès aléatoire (e.g. ALOHA (avec ou sans ACK) / CSMA)

TDMA / FDMA : débit constant -> utile pour téléphonie

Un reseau d'accès a une topologie arborescente.

ADSL : que des équipements actifs de réseaux

pour user entre dans le rezo : slot temporel laissé libre (tirage aléatoire temporel pour savoir qui rejoint en 1er puis en 2e...)

== modélisation 
(partie la + importante)

Le but est d'essayer de retenir ce qui est fondamental pour modéliser => simplifier le rézo

nécessite le plus d'expertise dans le domaine des rezo

pour un modèle pour un rezo il peut y a voir plusieurs modèles : on décide en fonction des critères de perf

plusieurs étude de perf en fonction des critères

== Méthode générale


#image("images/methode_gen.png", width: 65%)


= Analyse opérationnelle

== Chaîne de Markov à temps discret


#def([Processus stochastique: #linebreak()$(X_n, n in NN) $ à temps discret à espace d'états discret sera dit chaîne de Markov à temps discret si 

$forall (i_1, .., i_n, s) in  E^(n+1), PP(X_(n+1)=s | X_n = x_n,.. ,X_1 = x_1) = PP (X_(n+1) = s | X_n = n)$])


#def([Une chaîne de Markov $(X_n, n in NN)$ sera dite *homogène* si $forall(i,j)in E^2$ $forall(n,k)in NN^2$

$PP(X_(n+k+1)=i | X_(n+k) = j) = PP (X_(n+1) = i | X_n = j) = p_(i,j)$


$p_(i,j)$ = probabilité de transition de i à j \

$PP (p_"ij")$ matrice de transition. C'est une matrice stochastique . \ ])



Les valeurs propres d'une matrice stochastique sont dans le disque unité, et elles admettent 1 comme valeur propre. (théorème de Perron-Frobenius _je suis déjà duper_)

== Représentation des chaînes de Markov à temps discret (homogène)

Deux choix possibles :
- par sa matrice de transition P
- par un graphe orienté valué _le prof a vraiment mis "valué"_
  + état $<->$ transition
  + transition $<->$ flèches
  + probabilités de transition $<->$ poids

 #figure(diagram(
    node-stroke: .1em,
    node-fill: white,
    spacing: 4em,

    // Définition des nœuds (bulles)
    node((0,0),$0$),
    node((2,0),$1$),

    // Définiton des arrêtes 

    edge((0,0),(2,0),0.5,bend : 20deg,"-|>"),
    edge((2,0),(0,0),0.2,bend : 20deg,"-|>"),
    edge((2,0),(2,0),bend: -130deg,loop-angle : 180deg,$0.8$, "-|>"),
    edge((0,0),(0,0), bend: 130deg,loop-angle : -180deg,$0.5$,"<|-")
    
),caption: [graphe de démonstration]) <graphe1>


$ P = mat(
  0.5, 0.5;
  0.2, 0.8;
)$

== Evolution d'une CMTD (Chaine de Markov a Temps Discret)

- $Pi^(k)_n = PP(X_n = k)$

- $Pi^((k))=(Pi^(k)_1,..,Pi_n^k)$ distribution àl'instant k

- $Pi^(k+1)_n = sum_(j in E) Pi^(k)_j dot PP(X_(k+1) = n | X_k = j)$

- *$Pi^(k+1) = Pi^(k) dot P$*


- $Pi^(0)$ distribution à l'instant 0.

- $Pi^(k) = Pi^(0)P^k$

#linebreak()

=== Existence en régime permanent

$exists ? lim_(k->infinity) Pi^(k)_n = Pi_n$

(on sait pas si elle existe)

$Pi = (Pi_1,..,Pi_n,..)$ distribution en régime permanent


S'il y a convergence, alors *$Pi = Pi dot PP $*
et $Pi(II - PP) = emptyset$ ($II$ est un neutre au sens de la multiplication (genre 1 mais pour les ensembles) )

$norm(Pi)_1 = 1 = abs(Pi)$

Application au #ref(<graphe1>, supplement: "graphe de démonstrtation : Fig")

$Pi_0 = 0.5 Pi_0 + 0.2Pi_1  &=> 0.5 Pi_0 = 0.2 Pi_1 \

&=> Pi_0 = 0.4 Pi_1 (1) $


$Pi_1 = 0.5 Pi_0 +0.8Pi_1$      

$Pi_0 + Pi_1 = 1  &=> 1.4 Pi_1 = 1 "D'après (1)"\

&=> Pi_0 = 2/7  "et" P_1 = 5/7$

    #linebreak()

=== Classification sur les (états des) CMTD

*Irréductibilité :* Une CMTD sera irréductible si le graphe associé est *fortement connexe*. 
#grid(
  columns: 2, column-gutter : 10mm ,
  $M=m_"ij"\
  M^2$, 
  $m_"ij" = cases(1 "si" p_"ij" >0,
                  0 "si" p_"ij" = 0,
                )$
)
   
On utilise des algorithmes de fermeture transitive mais
- complexité élevée
- ne fonctionne que pour des graphes comportant un nombre fini d'états
 Dans la pratique, on saura par construction n le graphe est fortement connexe.


 #figure(
   diagram(
    node-stroke: .1em,
    node-fill: white,
    spacing: 4em,

    // Définition des nœuds (bulles)
    node((0,0), `0`),
    node((2,0), `1`),
    node((1,1),`2`),

    // Définition des transitions
    edge((0,0), (2,0),bend: 20deg, `1`, "-|>"),
    edge((2,0), (0,0), bend : 20deg , `1-p`, "-|>"),
    edge((0,0), (1,1),`p`,"-|>",label-side : right),
    edge((1,1), (2,0),$alpha$,"-|>", label-side : right),
    edge((1,1),(1,1), "-|>", $1-alpha$, bend : -130deg)
    
), caption: [Graphe connexe sous conditions]
 )<graphe2>


#grid(
  columns: 2, column-gutter: 10mm,
  $P= mat(
  0, 1-p, p;
  1, 0, 0;
  0, alpha, 1-alpha;
) $,
$0<=p<=1 \
0<= alpha <= 1$
)



Pour que @graphe2[le graphe] soit fortement connexe ici il faut deux conditions :
+ $ p > 0 $
+ $ alpha > 0 $
$p>0$ et $alpha > 0$, $exists$ un chemin entre : 2 et 1,2 et 0, 2 et 2 et de même pour les trois états

=== Périodicité état état : 

Pour un état j d'un CMTD : 

- $k_j$ = pgcd{longueurs des cycles relatifs  à ij }

- $k_j = 1$, j est dit apériodique

- $k_j > 1$, j est dit périodique de période $k_j$

Si tous les états sont a, j est dit périodique de pépériodiques, la chaîne est apériodique.
Si tout les états sont périodiques de même période, elle est dite périodique de période k.


Pour notre chaîne n°@graphe2[] Si $alpha < 1$ on a un cycle 2-2 de longueur 1 $=>$ état "2" apériodique

 Si $alpha=1 "le cycle est alors:" 2-1-0-2 "il est de longueur 3"$ alors  on a le PGCD de 5 et 3 = 1 
  - $=>$ état "2" apériodique

Si $p < 1 "cycle:" 2-1-0-1-0-2$ cycle de longueur 5. 
  - $=>$ état "2"  apériodique.

Si p = 1 les cycles sont de la forme 2-1-0-2 || 2-1-0-2 de longueur 3 maximum 
  - $=>$ état "2" périodique de période 3

=== États récurrent, états transitoires :

On notre pour un état f d'un CMTD

- $ f^(k)_1  = PP "(le 1er retour en 1 se fait en k pas de temps)"$

- $f^k = PP (X_(n+k) = j, X_(n+k-1) != j, X_(n+k+1) != j | X_n = j )$

- $f_j = sum_(k=1)^(+infinity) f_j^((k))$

- $f_j$ la probabilité de revenir en j.

- $f_j < 1 =>$ j est dit transitive

- $f_j = 1 =>$  j est récurrent 


Pour un état récurrent, on note $M_j$ le temps moyen du 1er retour en j.

$M_j = sum_(k=1)^(+infinity) k dot f^k_j$ 

- Si $M_j< + infinity$ j est dit récurrent non nul.
- Si $M_j -> (+infinity)$, j est dit récurrent nul

#figure(
  diagram(
    node-stroke: .1em,
    spacing: 4em,
    node-fill : gradient.radial(white, white, center: (30%, 20%)),
    
    node((0,0), $0$),
    node((1,0),$1$),
    node((2,0),$2$),
    node((3,0), $dots$, stroke : 0em),
    node((4,0),"k"),
    node((5,0),"k+1", shape:circle),
    node((6,0), $$, stroke : 0em),

    edge((0,0),(1,0),bend : 20deg, $p$, "-|>"),
    edge((1,0),(2,0),bend : 20deg, $p$, "-|>"),
    edge((2,0),(3,0),bend : 20deg, $p$, "-|>"),
    edge((3,0),(4,0),bend : 20deg, $p$, "-|>"),
    edge((4,0),(5,0),bend : 20deg, $p$, "-|>"),
    edge((5,0),(6,0),bend : 20deg, $p$, "-|>"),

    edge((6,0),(5,0), bend: 20deg, $q$, "-|>"),
    edge((5,0),(4,0), bend: 20deg, $q$, "-|>"),
    edge((4,0),(3,0), bend: 20deg, $q$, "-|>"),
    edge((3,0),(2,0), bend: 20deg, $q$, "-|>"),
    edge((2,0),(1,0), bend: 20deg, $q$, "-|>"),
    edge((1,0),(0,0), bend: 20deg, $q$, "-|>"),

    edge((0,0),(0,0), bend : 130deg, loop-angle : -180deg, "<|-", $q$)
  ), caption: [Graphe 3]
)<graphe3>

 #grid(
  columns: 2,column-gutter: 10mm,
    $p + q = 1 $, $0<= p<=1$
)

Pour que le graphe soit fortement connexe, il faut et il suffit 
$ 0<p<1 $

- Si $ p>q <=>  p > 1/2 =>$ les états sont transitoires.

- Si $p=q=1/2: =>$ les états sont récurrents nuls 

- si $p<1/2 =>$ les états sont récurrents non nuls.

*Graph 4*

- $f^((1))_1 = 0$

- $f^((2))_1= (1-p)$

- $f^((3))_1= p dot alpha$

- $f^((k+3))_1 = p dot alpha dot (1-alpha)^k$

- $f_1 = (1-p) + p dot alpha dot sum_(k=0)^(+infinity) (1-alpha)^k =  (1-p) + p dot alpha dot 1/alpha = 1 "(duh)" $ 

#align(center)[$
M_1 &= 2 dot (1-p) + sum_(k=0)^(+infinity)(k+3) dot p dot alpha dot (1- alpha) \


&=2 dot (1-p) +p dot alpha dot sum_(k= 0)^ (+infinity) (k+3)(1-alpha)^k\


&=2 dot (1-p) + p dot alpha dot sum_(k=0)^(+infinity)(k+3) dot beta^k\


&=2 dot (1-p) + p dot alpha dot sum_(k=0)^(+infinity)(k+2+1) dot beta^k\


&=2 dot (1-p) +  2 dot p + p dot alpha dot sum_(k=0)^(+infinity) (k+1)dot beta^k\


 &= 2 + p dot alpha d/(d beta) dot sum_(k = 0)^(+infinity) beta^(k+1) " car "(k+1) dot beta^k = d/(d beta) beta^(k+1) "puis on permute la somme et la dérivée"\


 &= 2 + p dot alpha dot d/(d beta)  sum_(k=0)^(+ infinity)beta^k\

 &= 2 + p dot alpha dot 1/(1 - p)^2\

 &= 2 + p/alpha^2 = 2 + p/alpha\

 &= 2 + p^alpha/alpha = (2alpha+p)/alpha$]

#prop([*(admise)* Les états d'1 CMTD homogène irréductible sont

#grid(
  columns : 3,column-gutter: 10mm,
  $ cases(- "tous transitoire",
  - "tous récurrents nuls",
  - "tous récurrents non nul",
)$, "ou",
$ cases(- "tous périodiques de même période",
  - "tous apériodique",
)$
)])




*Idée de preuve (périodicité)*

$ c_"ji" = abs(cal(C)_"ji") $

$ c_"ij" = abs(cal(C)_"ij") $


*Graph5*

Soit $cal(C)_i$ un chemin périodique relatif à l'état i (multiple de k).

$cal(C)_"ji" || cal(C)_"ij"$ cycle relatif à f(?) plutot j nn ?

$abs(cal(C)_"ji" || cal(C)_"ij")$ multiple de $k_j$ 

#h(5mm)$ = c_"ji"+c_"ij"$
\

#linebreak()

$cal(C)_"ji" || cal(C)_"i" ||  cal(C)_"ij"$ cycle relatif à ij \
$c_"ji"+ c_i + c_"ij"$ multiple de $k_j$


$c_i$ multiple de $k_i$

$=> k_i$ multiple de $k_j$ \
idem $k_j$ multiple de $k_i$
$=> k_i = k_ j$



#prop([*(admise)* (Pour une CMTD)

irréductible qui comporte un nombre fini d'état, les états sont tous récurrents non nuls])



#def([Un état d'une CMTD 


irréductible qui est récursive non nuls et apériodique est dit ergodique si tous les états sont ergodiques la chaîne est ergodique ])

#theo([*(admis)* Pour une chaîne ergodique $Pi_j^((n)) ->_(n -> +infinity) Pi_j > 0$ 

$Pi$ solution unique de $cases(Pi dot P = Pi,
abs(Pi) = 1,
)$ ; $Pi_j = 1/M_j$ \
indépendant de $Pi^((0))$

$cal(D)$ans tous les cas si la chaine est irréductible et apériodique il y a convergence, mais si les états sont transitoires ou récurents nuls, $Pi_j^n ->_(n -> +infinity) 0, forall j$])




*Remarque pratique*
Si une CMTD irréductible et périodique admet une solution unique et positive (strictement) à l'équation donc 

$ Pi dot P = Pi $
$ abs(Pi) = 1 "alors elle sera ergodique" $



*Pb lié à la périodicité* 

<grpahe6> 

chaine inéductible
états récurrents non nuls
$M_0 = M_1 = M_2 = M_3$

#grid(
  columns: 2,column-gutter: 10mm, gutter: 5mm,
  $Pi dot I = Pi $, $ P= mat(
  0, 0, 1;
  1, 0, 0;
  0, 1, 0;
) $,$cases(Pi_0 = Pi_1,
Pi_1 = Pi_2,
Pi_2 = Pi_3)$ ,
$Pi_0 = Pi_1 = Pi_2 = 1/3$
)



#grid(
  columns: 2, column-gutter: 10mm,
  $Pi^(0) = (1,0,0)$, $Pi^(1) = (0, 1, 0) $
)





propotion de temps passé dans les états

- 1 étape (1 0 0)

- 2e étape (1/2, 0, 1/2)

- 3e étpe (1/3, 1/3, 1/3)



$ Pi^((0))$ distribution à l'instant 0.

$Pi^((0)) = (Pi^((0)))_0 , Pi^((0))_1, Pi^((0))_2) = Pi^((3)) = Pi^((3k))$

$Pi^(1)=(Pi_1^(0),Pi_2^(0),Pi_0^(0)) = Pi^(4)=Pi^(3k+1)$ 


$Pi^((2)) = (Pi^((0)))_2 , Pi^((0))_0, Pi^((0))_1) = Pi^((5)) = Pi^((3k +2))$

$Pi^((k)$ n'admet pas de limite quand $k -> + infinity$ 




#diagram(
    node-stroke: .1em,
    node-fill: white,
    spacing: 4em,

    // Définition des nœuds (bulles)
    node((0,0), `0`),
    node((2,0), `1`),
    node((1,1),`2`),

    // Définition des transitions
    edge((0,0), (2,0),bend: 20deg, `1`, "-|>"),
    edge((2,0), (0,0), bend : 20deg , `1-p`, "-|>"),
    edge((0,0), (1,1),`p`,"-|>",label-side : right),
    edge((1,1), (2,0),$alpha$,"-|>", label-side : right)
    
)

 $ P= mat(
  0, 1-p, p;
  1, 0, 0;
  0, alpha, 1-alpha;
)
cases(Pi dot PP= Pi,
abs(Pi)=1)$


$Pi_0 = Pi_1$

$Pi_1=(1-p)dot Pi_0 + alpha dot Pi_2$ avec $p dot Pi_0= alpha dot Pi_2$

$Pi_2 = p Pi_0 + (1 - alpha) Pi_2$   et $cancel(p Pi_0 = alpha Pi_2)$

$Pi_0 + Pi_1 + Pi_2 = 1$

$Pi_0 (2 + p/alpha) = 1 => Pi_0 = alpha/(p + 2 dot alpha)$

$ Pi_1 = alpha/(p + 2 dot alpha) = 1/M_1$ ?? qui est M1 ? en bas à droite


$ Pi_2 = alpha/(p + 2 dot alpha)$





= Chapitre 2 : Chaîne de Markov à temps continu

#def([Un processus stochastique $(X_t,t>=0)$ à temps continu et à espace d'états discret E sera dit chaîne de Markov à temps continu (CMTC)



Si $forall t_1 < t_2 < .. < t_n < t$, $forall (i_1,...,i_n,j) in E^(n+1)$

$PP(X_t = j | X_t_n = i_n, X_t_1 = i_1) = PP(X_t = j | X_t_n = i_n) $ 
])

#def([ Une CMTC sera dite homogène si :

$forall (s,t,u) in RR^+, s<t, forall i,j in E^2$

$PP(X_(t+u)=j | X_(s+u) = i)= PP(X_j = j | X_s=i) = p_(i j)(t-s)$


 probabilité de transition de i à j sur une durée (t-s).

$P(t) = (p_"ij" (t))$ matrice de transition sur une durée t. (matrice stocahstique)
])


=== Evolution d'un CMTC


On note : \
$Pi_1(t) = PP(X_t = j)$

$Pi(t) = (Pi_1(t), ..., Pi_j (t), ...)$ distribution à l'instant t.

$Pi(t) = Pi(0)P(t)$

$Pi (t+h) = Pi(t) dot PP(h)$

$(Pi(t+h) - Pi(t))/h = Pi(t) dot (PP(h) - II)/h$

Si les limites existent
$Pi'(t) = Pi(t) dot Q\
Q = lim_(h->0) (P(h)-I)/h$


Q générateur infinitésimal.

$i != j$  et  $ q_(i j) = lim_(h-> 0) (p_(i j)(h))/h$

appelé taux de transition (instantanée) de  i à j


$q_"ij" = lim_(h->0) (p_"ij" -1 )/h\
q_"ij"=lim_(h->0) (1 - sum_(j!=i) p_(i j) (h) -1)/h $

$q_"ij"= - sum_(i != j) lim_(h-> 0) (p_(i j)(h))/h$

$q_"ij"=-sum_(j!=i) q_"ij"$

$sum_(j in E) q"ij" = 0$ => la matrice Q admet $emptyset$ comme valeur propre


$Pi_j (t +d t) =  Pi_j(t) + Pi_j '(t) d t + o("dt")$


$Pi_j (t +d t)  = Pi_j (t) + sum_(i in EE) q_(i j) Pi_i (t) d t + o("dt")$

$Pi_j (t +d t) = (1+q_"jj"  dot d t) dot Pi_j (t)+ sum_(i!=j) q_"ij" dot Pi_i (t) dot d t + o(d t)$



== Représentation d'une chaîne de Markov à temps homogène

- Q sont générateur infinitésimal
- par un graphe orienté et valué

sommets $<--> $ états

flèches $<--> $ transitions instantanées

poids $<--> $ taux de transition > 0


#diagram(
    node-stroke: .1em,
    node-fill: white,
    spacing: 4em,

    // Définition des nœuds (bulles)
    node((0,0), `0`),
    node((1,0), `1`),

    // Définition des transitions
    edge((0,0), (1,0),bend: 30deg, `λ`, "-|>"),
    edge((1,0), (0,0), bend : 30deg , `ν`, "-|>")
)



$Q = mat(-lambda, lambda;
mu, - mu;)$


=== Régime permanent

existe-t-il $Pi_i (t) ->_(t-> infinity) Pi_j$ ?

$Pi = (Pi_1,...,Pi_j,...)$

$ Pi'(t) = Pi(t) Q$ 


- $t-> infinity$

$0 < Pi dot Q$

$(abs(Pi) = 1)$

$0 = - lambda Pi_0 + mu Pi_1$
$0= lambda Pi_0 + mu Pi_1$

On rajoute $ Pi_0 + Pi_1 = 1 $

$Pi_0 = mu/(lambda + mu); Pi_1 = lambda/"récurrentmu")$


== Classification des (états d'une) CMTC

- Irréductibilité = même définition que pour les CMTD

=== Etats récurrents transitoires

$F_j (t)$ probabilité que le premier retour en j ait lieu en une durée $<=$  t.



$F_j = integral_(t=0)^(infinity) d F_j(t)$

- Si $F_j < 1$ j est dit transitoire
- Si $F_j = 1$ j est dit récurrent

=== Etats récurrents nuls et non nuls

$M_j = integral^(+ infinity) t d F_j(t)$ temps moyen de 1er retour en j.

$M_j < infinity$ j est dit récurrent *non nul* \
$M_j -> infinity$ j est dit récurrent *nul*

#prop([*(admise)* 
Pour un CMTC irréductible, les états sont soit :
- tous récurrents non nuls
- tous récurrents nuls
- tous transitoires])

#prop([Pour un CMTC irréductible qui comporte un nombre fini d'états, tous les états sont RNN.])


#def([ un état récurrent non nul (RNN) est dit ergodique si tout les états sont ergodiques, la chaine est ergodique.])

#theo([*(admis)* Pour une chaîne ergodique, il y a convergence $ Pi_j (t) -> Pi_j > 0 $
$Pi$ solution de $cases(Pi Q = 0, abs(Pi)=1)$ indépendamment de la distribution initiale $Pi(0)$



Si la chaîne est irréductible, mais que les états sont transitoires ou récurrents nuls. Alors il y a convergence:
$Pi_j(t) ->_(t-> infinity) 0$])





#cor([Si on a 
- un nombre fini d'états
- la chaîne est irréductible

Alors la chaîne est ergodique.


Sinon, s on a :
- un nombre infini d'états
- la chaîne est irréductible
- Si $Pi Q = 0$, et que $abs(Pi) = 1$, admet 1 solution positive

Alors la chaîne est ergodique.]) 



Exemple 1 : Les processus de naissance et de mort $(X_t, t>=0)$ CMTC à états E = (0,1,...)

sera dit processus de naissance et de à $forall i , j abs(i-j) > 1 "avec" q_"ij" = 0$

$lambda_i = q_(i,j+1)$ est appelé *taux de naissance dans l'état i*

$mu_i = q_i,j+1$ est appelé *taux de mort dans l'état i*


#figure(
  image("images/GraphAntoine.jpg"),
)


Exemple 2 : Le processus de Poisson

C'est un processus de naissance pur à taux de naissance constant $lambda$. C'est un processus de comptage, on compte les naissances à partir d'un instant initial t_0 = 0
(N(t), t$>=0$), distribution initiale $Pi(0) = (1,0...0...)$


#figure(
  image("images/Graph_Evann.jpg"),
)


Ce n'est pas un processus ergodique. On va regarder uniquement le régime transitoire $Pi(t)$

$Pi_0 (t + "dt") = Pi_0 (t)(1-lambda"dt") + o("dt")$

$Pi_1 ( t + d t) = Pi_0 ( t) lambda"dt" + Pi_1 (t) (1-lambda"dt") + o("dt")$

$Pi_(k+1) (t + "dt") = Pi_k (t)lambda"dt" + Pi_(k+1)(t) (1-lambda"dt") + o("dt")$

Équations différentielles:

$Pi'_0(t) - lambda Pi_0(t)$

$Pi'_1(t) = lambda Pi_0(t) - lambda Pi_1(t)$

$Pi'_(k+1)(t) =lambda Pi_k(t) - lambda Pi_(k+1)(t) forall k>= 1$

Début de résolution (on veut retrouver la loi de poisson):

$ Pi_0 (t) &= K exp(-lambda t)\

Pi_0 (0) &= 1\

Pi_0(t) &= exp(-lambda t)\

Pi_1(t) &= K(t)exp(-lambda t)\

exp(-lambda t ) (K'(t) - cancel(lambda K(t))) &= lambda exp(-lambda t) cancel( - lambda K(t) exp(-lambda t))\

K'(t) &= lambda\
& => K(t) = lambda t + C\

Pi_1(t) &= (lambda t) exp(-lambda t)\

Pi_k(t) &= (lambda t)^k/k! dot exp(- lambda t)\

Pi_(k+1) (t) &= K(t) exp(-lambda t)


exp(- lambda t) {  K'(t)- lambda cancel(K(t)) } \
&= lambda dot (lambda t)^t/k! dot exp(- lambda t) - lambda K(t) exp(-lambda t)\

K'(t) &= lambda (lambda t)^k / k!\

K(t) &= (lambda t)^k / (k+1)! +C\

K(0)&= 0 $

$Pi_t (exp(-lambda t), lambda t exp(-lambda t), ..., (lambda +1)^k/k! exp(-lambda t) ...) $

N(t) suit une loi de Poisson $lambda t$ 

$E(N(t)) = lambda t; "Var"(N(t)) = lambda t$

=== Temps entre naissances successives

$tilde(t)$ temps avant la 1ère naissance.

$F_(tilde(t_1)) (t) = 1 - exp(-lambda t), t> =0 $

$f_tilde(t_1) (t) =  lambda exp(-lambda t), t>= 0$

$tilde(t_1)  ~ exp(lambda)$

$E(tilde(t_1)) = 1/lambda$

$"Var"(tilde(t_1)) = 1/lambda^2$

$C_tilde(t_1) ^2 = "Var"(tilde(t_1))/E(tilde(t_1) ^2) = 1$


On change de processus pour les naissances suivantes en comptant les naissances à partir de ces instants de naissances successifs.


De façon similaire, $tilde(t_k)$ le temps entre la naissance n°(k-1) et n°k.
$ tilde(t_k) ~ exp(lambda) $

*Exemple 3 :*  On considère le processus de naissance et de mort à  taux de naissance constant $lambda > 0$ et à taux de mort constant $mu > 0$


#figure(
  image("images/Graph_personne.jpg"),
)


$lambda > 0, mu >0$, graphe fortement connexe chaîne irréductible

#figure(
  image("images/Matric_personne.jpg"),
)

$ Pi Q &= 0 \
&cases(-lambda Pi_0 = mu Pi_1 =0, lambda Pi_0 - (lambda + mu)Pi_1 + mu Pi_2 = 0)\

lambda Pi_(k-1) - (lambda + mu) Pi_k + mu Pi_(k+1) &= 0\ 


Pi_1 &= lambda/mu Pi_0\

Pi_2 &= lambda/mu Pi_1 = (lambda/mu)^2 Pi_0$

Donc de proche en proche:
$Pi_(k+1) = lambda/mu Pi_k = (lambda/mu)^k Pi_0$

$sum_k Pi_k = 1$

Donc on en déduit:

$Pi_0(sum_(k>=0) (lambda/mu)^k ) = 1$

Comme c'est une somme géométrique:

Si $lambda/mu < 1, "alors:" Pi_0 = 1/(1-lambda/mu) = 1$



$Pi_0 = (1-lambda/mu)$ \
$Pi_k = (1-lambda/mu)(lambda/mu)^k, k >=0$


=== Méthode des coupes

Soit une chaîne ergodique (N(t), t>=0) quelle que soit la coupe C dans le graphe d'états $C=(E_1,E_2)$

$E_1 inter E = 0; E_1 union E_2 = E$

$sum_(j in E_1) sum_(i in E_2) Pi_j q_"ji" = sum_(j in E_1) sum_(i in E_2) Pi_i q_"ij"$

#figure(
  image("images/E1_E2.jpg"),
)

*Idée de preuve :* 

$0=Pi Q$ est une méthode de couple 

$ forall j in E, sum_(i in E) Pi_i q_"ij" &= 0\

Pi_j q_"jj" + sum(i!=j) Pi_i q_"ij" &= 0\

-sum_(i!=j) Pi_j q_"ji" + sum_(i!=j) Pi_i q_"ij" &=0\


sum_(i!=j) Pi_i q_("ij") &= sum_(i!=j) Pi_j q_("ji")" et "C = {{j},E\\{j}}\

forall j in E_1:
sum_(i in E) Pi_i q_("ij") &= 0\

sum_(j in E_1) sum_(i in E) Pi_i q("ij") &= 0\

sum_(j in E_1) sum_(i in E_1) Pi_i q_"ij" + sum_(j in E_1) sum_(i in E_2) Pi_i q_"ij" &= 0\

sum_(i in E_1) sum_(j in E_1) Pi_j q_("ji") &= sum_(j in E_1) Pi_j sum_(i in E_1) q_("ji")\


sum_(i in E_1) q_"ji" &= q_"jj" + sum_(i in E_1) q_"ji" - sum_(i in E) q"ji"\

&=-sum_(i in E_2) q_"ji"\

sum_(j in E_1) sum_(j in E_2) Pi_i q_"ij" &= sum_(j in E_1) sum_(i in E_2) Pi_j q_"ji"$



#figure(
  image("images/IMG_20250304_094702754.jpg"),
)

#figure(
  image("images/IMG_20250304_094942746(1).jpg"),
)



== Files d'Attente Simples

#def([Une file d'attente est défini par un flux de #underline[clients] qui demandent un #underline[service] rendu par un certain nombre de guichets (ou #underline[serveurs]) mais qui suite à des restrictions sur le nombre de serveurs ou le type de service sont amenés à attendre. 

On suppose qu'un serveur ne sert qu'un client à la fois et qu'un client n'est servi que part un serveur à la fois.

Les clients peuvent être regroupés en #underline[classes] de service correspondant à  un niveau de priorité, une durée de service etc...])

== Notation de Kendall des files d'attente :

=== Variables utilisées:

 
Paramètres obligatoires : A,D,m. 

Pour les 3 autres on met des valeurs par défaut.


- A = (caractérisation) loi d'arrivées des clients dans la file ; 
  - M : Poisson (Memoryless) ;
  - D : Constant (Deterministe) ;
  - G : Quelconque (Générale) ;
  - $dots$
- B = loi de la durée du service ;
  - M : exponnetielle (Memoryless) ;
  - D : Constant ;
  - G : General ;
  - $dots$
- m =  nombre de serveurs ;

- K = capacité de la file ;
  - #underline[par défaut] $infinity$.
 #figure(
   image("images/file_attente_1.jpg", width: 50%),
 )
 #diagram(
   node-stroke : 0.1em,
   node((0,0),$$,stroke : 0em),
   node((1,0), shape : rect, "  |  ", stroke : 0.1em),
   node((2,0.5), shape : rect, $X$),
   node((2,-0.5), shape : rect, $X$),
   node((3,0)),

   edge((0,0),(1,0),"-|>"),
   edge((1,0),(2,0.5),"-|>"),
   edge((1,0),(2,-0.5),"-|>"),
   edge((2,0.5),(3,0),"-|>"),
   edge((2,-0.5),(3,0),"-|>"),
   edge((3,0),(4,0),"-|>")
 )
$<------->$
 
 - F =  discipline de service (ordonnanceur) ;
  - FCFS (First Come First Served) (même chose que FIFO mais ne pas dire FIFO !!!) #underline[par défaut] ;
  - LCFS (Last Come First Served): si système saturé, quelques uns vont quand même réussir à passer (meilleure qualité d'expérience) ;
  - Quantum ;
  - Processor Sharing (PS) : cas limite du Quantum ;
  - Mécanismes de priorité : absolue, préemptive (si une prio plus élevée arrive: on tej celle en cours pour passer la prio +) ;
  - $dots$  
- N = Taille de la population: nombre max de client intéressés/susceptibles d'aller dans la file (#underline[par défaut]: $infinity$).

#underline[exemple de limitation] : 
  - environnement mobile. Seuls les utilisateurs de la cellule sont susceptibles de communiquer.
  - Réseau paquet avec contrôle de flux. Chaque communication n'a droit qu'à K paquets/accusé de réception $=>$ Nombre total de paquets dans le réseau est limité.
exemple : 


 #diagram(
   node-stroke : 0.1em,
   node((0,0),$$,stroke : 0em),
   node((1,0), shape : rect, "  |  ", stroke : 0.1em),
   node((2,0.5), shape : rect, $X$),
   node((2,-0.5), shape : rect, $X$),
   node((2,-0.9), $mu$, stroke : 0em),
   node((2,0.9), $mu$, stroke : 0em),

   edge((0,0),(1,0),"-|>"),
   edge((1,0),(2,0.5),"-|>"),
   edge((1,0),(2,-0.5),"-|>"),
   edge((2,0.5),(3,0),"-|>"),
   edge((2,-0.5),(3,0),"-|>"),
   edge((3,0),(4,0),"-|>")
 )


= Analyse opérationnelle (loi de Little) (Chapitre 3??)

Soit un système traitant des requêtes.

#diagram(
  node-shape : rect,
  node-stroke : 0.1em,
  node((1,0), [$overline(R)$, $overline(L)$]),

  edge((0,0),(1,0), $lambda$,"-|>"),
  edge((1,0),(2,0), $Lambda$,"-|>"),
)

 - $lambda :$ débit d'arrivée des requêtes
 - $Lambda :$ débit de sortie des requêtes 
 - $overline(LL) :$ nombre moyen de requêtes dans le système
 - $overline(R) :$ temps moyen posé par les requêtes dans le système.

$overline(LL) = Lambda dot overline(R)$


#underline[Illustration] : Soit 1 file d'attente simple avec un serveur, FCFS

#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), " | | "),
  node((2,0),$X$),

  edge((0,0),(1,0), "-|>"),
  edge((1,0),(2,0), "-|>"),
  edge((2,0), (3,0), "-|>")
)

#figure(
  image("images/graphe_L_t.jpg", width: 50%),
)
// je give up pour ça
// tkt je fais sur ma tablette

- $overline(LL_T) :$ nombre moyen de clients dans la file entre 0 et T ;
- $M_T :$ nombre de clients servis entre 0 et T ;
- $overline(R_T) =$ temps moyen de réponse entre 0 et T ;
- $r_i :$ temps de réponse du client i ;
- $Lambda_T$ = débit(moyen) entre  0  et T (de sortie).

$Lambda_T &= M_T/T\

overline(R_T) &= 1/M_T dot sum^(M_T)_(i = 1) r_i\

overline(LL_T) &= 1/T dot integral^T_(t=0) L(t) d t$

#figure(
  image("images/graphe_l_t_color.jpg",width: 70%),
)
Donc,

$ integral^(T)_(t=0) L(t) d t = sum^(M_T)_(i=1)r_i$


$overline(L_T) &= 1/T dot sum_(i=1)^M_T r_i = M_T / T dot 1/M_i dot sum_(i=1)^M_T r_i\
 
 &= Lambda_T dot overline(R_T)$

En faisant tendre $T -> infinity$

$overline(L) = Lambda dot overline(R)$


Pour cela, il faut que le système se vide une infinité de fois

Utilisation de la loi de $underline("Little")$ au serveur d'une file simple avec un seul serveur



#theo([*Théorème de Chang-Lavenberg* 

#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), " | "),
  node((2,0),$X$),

  edge((0,0),(1,0), "-|>"),
  edge((1,0),(2,0), "-|>"),
  edge((2,0), (3,0), "-|>")
)

- $Lambda$ = débit de sortie
- $overline(LL_S) =$ nombre moyen de clients en service
- $overline(R_S) = overline(SS) =$ temps moyen de service
- U= taux d'occupation du serveur
$ overline(L_S) = overline(S) dot Lambda $
])


$overline(L_s) = (1-U) dot 0 + 1 dot U = U$ (attention homogénéité, U sans unité mais 1 est en nombre de clients comme $overline(L_s)$)

$U = overline(S) dot Lambda <= 1$ où: $Lambda <= 1/overline(S)$

=== Modèle de base pour les réseaux à commutation de Paquets

#diagram(
  node-shape : rect,
  node-stroke : 0.1em,

  node((1,0),$X$),
  node((2,0),$X$),

  edge((0.5,0.5),(1,0)),
  edge((0.5,-0.5),(1,0)),
  edge((1,0),(2,0),"=")
  
)

- Arrivées poissonnienne de taux $lambda$
- Durée des services suit une loi exponentielle de taux $mu$
- 1 serveur
- FCFS
- Capacité $infinity$
- taille population



#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), " | | "),
  node((2,-0.4),"u",stroke : 0em),
  node((2,0),$X$),

  edge((0,0),(1,0), "-|>",$lambda$),
  edge((1,0),(2,0), "-|>"),
  edge((2,0), (3,0), "-|>")
)




- $rho :$ charge de la file

$rho = lambda dot EE(S) = lambda/mu$

$EE(L) = ?$, $EE(R) = ?$

L(t), nombre de clients dans la file à t (L(t), t $>= 0$) est de 1 CMTC de type processus de naissance et de mort

*Arrivées*

$PP(1 "arrivée entre" t "et" t + d t) = lambda dot d t + o(d t)$

$PP(0 "arrivée entre" t "et" t + d t) = 1 - lambda dot d t + o(d t)$

$PP("Plus d'une arrivée entre" t "et" t + d t) = o(d t)$


*Départs/fins de service*

$PP(1 "sevice en cours à" t "se termine entre t et" t + d t) = mu dot d t + o(d t)$

$PP(1 "sevice en cours à" t "ne se termine pas entre t et" t + d t) = 1 - mu dot d t + o(d t)$

$PP$(2 fins de service entre t et t + dt) $<= mu^2 ("dt") + o("dt") = o("dt")$ 

$PP(0 "départ entre" t "et" t + d t) = 1 - mu dot d t + o(d t)$

$PP(1 "départ entre" t "et" t + d t) = mu dot d t + o(d t) => (L(t), t >= 0) = "CMTC"$

$PP(L(t+&"dt") = k+1 | L(t) = k>0)\
 &= lambda dot"dt" + o("dt") (1 - mu dot "dt" + o ("dt"))\
 &= lambda dot "dt" + o("dt")$ 

$PP(L(t + d t)= k-1 | L(t) = k > 0) = (1- lambda dot d t + o(d t))(mu dot d t + o(d t)) = mu dot d t + o(d t)$

$PP(L(t + d t)) = k | L(t) = k > 0) = (1- lambda dot d t + o(d t))( 1 - mu dot d t + o(d t)) = ("pas sur qu'il y ait un égal") (lambda dot d t + o("dt")(mu dot d  t + o("dt")))$

$PP(L(t+ d t) = k | L(t) = k) = 1 - (lambda - mu)dot d t + o(d t) $

C'est un processus de naissance et de mort
*Là y'a un graphe*
*deux* deux ???? OUI, deux
#figure(
  image("images/processus_1.jpg", width: 50%),
)

$ lambda > 0 "et" mu > 0 $ 

$lambda dot Pi_0 = mu dot Pi_1 => Pi_1 = lambda/mu dot Pi_0 = rho dot Pi_0$



$lambda dot Pi_1 = mu dot Pi_2 => Pi_2 = rho dot Pi_1 = rho^2 dot M_0$

$lambda dot Pi_k = mu dot Pi_(k+1) => Pi_(k+1) = lambda/mu dot Pi_k+1 = rho^(k+1) Pi_0$

$sum^inf_(k=0)Pi_k =1$

$Pi_0 dot (1 + rho + rho^2 + dots + rho^k + dots) = 1$



$E(L) = sum^(+infinity)_(k=0) k T'_k &= (1-rho)sum^(+infinity)_(k=1)k rho^k\
&=rho(1-rho) dot sum_(k=1)^(+infinity )k dot rho^(k-1)\
&= rho(1-e) d/(d rho) sum^(+infinity)_(k=0) rho^k\
E(L) &= rho/(1-rho)$

$EE(R) = E(L)/Lambda$

#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), " | | "),
  node((2,0.4),$mu$,stroke : 0em),
  node((2,0),$X$),

  edge((0,0),(1,0), "-|>",$lambda$),
  edge((1,0),(2,0), "-|>"),
  edge((2,0), (3,0), "-|>")
)

- Quand la file d'attente est vide:

$Lambda &= 0 dot Pi_0 + mu(1-Pi_0)   \
&= mu (1- (1 - rho)) = mu rho = mu lambda/mu\
&=lambda$

$E(R) &= E(L)/lambda\
&= (cancel(lambda)/mu)/(cancel(lambda) (1 - rho))\ 
&= 1/(mu (1- rho))\
E(R)&= 1/(mu-lambda)$




*Etude de la file M/M/1/N:*

#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), " | | "),
  node((2,-0.4),$mu$,stroke : 0em),
  node((2,0),$X$),
  

  edge((0,0),(1,0), "-|>",$lambda$),
  edge((1,0),(2,0), "-|>"),
  edge((2,0), (3,0), "-|>"),
  edge((0.5,0), (0.5,1), $tau$, "-|>")
)

#diagram(
    node-stroke: .1em,
    node-fill: white,
    spacing: 4em,

    // Définition des nœuds (bulles)
    node((0,0), `0`),
    node((1,0), `1`),
    node((1.5,0), $dots$, stroke : 0em),
    node((2,0), `N-1`, shape : circle),
    node((3,0), `N`),

    // Définition des transitions
    edge((0,0), (1,0),bend: 30deg, `λ`, "-|>"),
    edge((1,0), (0,0), bend : 30deg , `ν`, "-|>"),
    edge((2,0), (3,0),bend: 30deg, `λ`, "-|>"),
    edge((3,0), (2,0), bend : 30deg , `ν`, "-|>")
)


$lambda > 0 "et" mu >0 => $ irréductible / nombre fini d'état / ergodique (pas sure de la mise en forme)



//def ergodique : L'hypothèse ergodique, ou hypothèse d'ergodicité, est une hypothèse fondamentale de la physique statistique selon laquelle, à l'équilibre, la valeur moyenne d'une grandeur calculée de manière statistique est égale à la moyenne d'un très grand nombre de mesures prises dans le temps. WTFFF ???


//*pk la ya déf d'ergodique? parce que on sait pas ce que c'est* c'est dans la table du début


#grid(
  columns: 2, column-gutter: 10mm,
  [$lambda Pi_0 = mu Pi_1$

$lambda Pi_1 = mu Pi_2$

$dots$

$lambda Pi_(N-1) = mu Pi_N$

$Pi_0 + Pi_1 + dots + Pi_N = 1$],
  [$Pi _1 = rho Pi_0$

$Pi_2 = rho^2 Pi_0$

$dots$

$Pi_N = rho^N Pi_0$

$Pi_0 (1+rho + ... + rho^N) = 1$]
)





$rho != 1 $  $Pi_0 dot (1-rho^(N+1))/(1-rho) = 1$

On isole $Pi_0$:
$Pi_0 = (1-rho)/(1-rho^(N+1))$

Donc de proche en proche : $Pi_k = rho^k dot (1- rho)/(1-rho^(N+1))$ avec $mu >= k >= 0$


$rho = 1$ #h(10mm)  $Pi_0 = Pi_1 = Pi_2 = dots = Pi_N = 1/(N+1)$

$tau =  "(PASTA : Poisson Arrivals See Time Averages)"= Pi_N$ 
// JE SUIS DUPER, tkt t'es pas seul jpp ça le casse les couilles, je me fais chier


Average : 

$tau = 1/(N+1)$ #h(10mm) $rho = 1$

$tau = rho^N dot (1-rho)/(1-rho ^(N+1))$ #h(10mm) $rho != 1$


$XX = lambda dot Pi_N$

$tau_0 = XX/lambda = Pi_M$

$Lambda = mu dot (1 - Pi_0)$

$tau &= (lambda - Lambda)/lambda = 1 - Lambda/lambda\

 &= 1 - mu/lambda (1 - Pi_0) = 1 - 1/rho (1 - Pi_0)$

- $rho != 1$
$tau &= 1 - 1/rho (1-Pi_0)\
&= 1 - 1/rho (1- (1-rho)/(1-rho^(N+1)))\
&= 1 - 1/rho {(rho - rho^(N+1))/(1-rho^(N+1))}\
&= 1 - (1- rho^N)/(1- rho^(N+1))\

&= (1- rho^(N+1) - (1 - rho^(N)))/(1- rho^(N+1)) = rho^N dot (1-rho)/(1- rho^(N+1)) = M_N$


$tau (rho, N)&= rho^N (1-rho)/(1- rho^(N+1)) #h(3em)& rho != 1\
&= 1/(N+1) &rho = 1$

fonction croissante de $rho$ Par rapport à la charge

fonction décroissante de $rho$ //je sais pas pk il écrit des trucs contradictoires ici

$lim_(N-> infinity ) tau(rho,N) = lim_(N-> infinity) rho^N dot (1-rho)/(1-rho^(N+1))$

- Si $rho <1$ :
$lim_(N-> infinity) tau(1,N) = 0$

$lim_(N-> infinity) tau(rho,N) = lim_(N-> infinity) (rho-1)/(rho - 1/rho^N)$

- Si $rho>1$ :

$lim_(N-> infinity) tau(rho,N) = (rho - 1)/rho$



=== Modèles de base pour les réseaux "paquets"

#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), " | | "),
  node((2,-0.4),$mu$,stroke : 0em),
  node((2,0),$X$),
  

  edge((0,0),(1,0), "-|>",$lambda$),
  edge((1,0),(2,0), "-|>"),
  edge((2,0), (3,0), "-|>"),
  edge((0.5,0), (0.5,1), $tau$, "-|>")
)



$tau = Pi_N = 1/(N+1)$, $rho = 1$

$tau  = rho^n dot (1-rho)/(1-rho^(N+1))$, $rho != 1$

$(rho, tau^*) -> NN^*$

$tau^* >= rho^N dot (1-rho)/(1-rho^(N+1))$

En posant: $x = rho^N$

$tau^* >= x dot (1-rho)/(1-rho dot x)$

D'où: $(1-rho dot x)dot tau^* >= x(1-rho)$

et donc, en passant $rho dot x $ de l'autre coté:
$tau*>= x(1-rho+rho dot tau*)$

On isole alors x:
$rho^N = x <= tau^* /(1-rho + rho tau^*)$

$N dot log_10 (rho) <= log_10 ( tau*) - log_10 (1-rho +rho dot tau*)$

$N >= (log_10 (tau^*) - log_10 (1-rho+rho dot tau^*))/(log_10(rho))$

#box(
  stroke: red,
  inset: 10pt,
  height: 11mm
)[
  #block(
    $N^* = ceil.l ((log_10 (tau^*) - log_10 (1-rho + rho dot tau^*))/(log_10 (rho))) ceil.r$
  )
]
(arrondi au supérieur)
=== Modèles de base pour les réseaux à commutation de circuit


#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((1,0), $X$),
  node((2,0),$X$),
  

  edge((1,-0.1),(2,-0.1)),
  edge((1,0),(2,0)),
)

#diagram(
  node-shape: rect,
  node-stroke : 0.1em,

  node((2,-1), $X$),
  node((2,1),$X$),
  node((2,-1.4),$u$,stroke : 0em),
  
  
  edge((0,0),(1,0),"-|>",$lambda$),
  edge((1,0),(1,1),"-|>",$tau$),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0), $c$, label-side: right, label-pos:0%),
  edge((2.2,-1),(3,0), $1$, label-pos:0%),
  edge((3,0),(4,0),"-|>"),
  edge((2,0.1),(2,-0.1),"dotted")
)

Arrivées des appels -> loi de Poisson ($lambda$)

Durée des appels -> loi exponentielle ($mu$)

#underline[M/M/C/C]

On regarde le critère de performance au travers du taux de rejet $tau$.

$rho = lambda/mu$ est la charge, ie, le nombre moyen de communications si il n'y a pas de rejets. Il est exprimé en *Erlangs*.

On peut normaliser la charge: $rho_N = rho/c = lambda/(c dot mu)$. On exprime peu souvent en charge normalisée.


On pose $L(t)$ le nombre d'appels en cours, et on a: $(L(t), t >= 0)$ une CMTC de type processus de naissance et de mort.

Ce qui fera evoluer le nombre d'appels dans la chaine est l'arrivée ou la fin d'un appel.


=== Arrivées poissonniennes

$PP(1 "arrivée entre" t "et" t + d t ) = lambda d t + o(d t)$

$PP(0 "arrivée entre" t "et" t + d t ) = 1 - lambda d t + o(d t)$


Tout le reste est négligeable

=== Fin d'appels et départs


$PP(1 "appel en cours à" t  "se termine entre" t "et" t + d t ) = mu d t + o(d t)$


$PP(1 "appel en cours à" t  "ne se termine pas entre" t "et" t + d t ) = 1 - mu d t + o(d t)$


$PP(1 "fin d'appel entre"& t "et" t + d t | L(t) >= k > 0 ) \
&= mat(k; 1) dot (mu d t + o(d t))(1 - mu d t + o(d t))^(k-1)\
&= k dot mu dot d"t" +o(d"t")$


$PP(0 "fin d'appel entre" t "et" t + d t) &= (1 - mu d t + o(d t))^k\
&=1 - k mu d t + o(d t)$

$PP(2 "fins d'appel entre "t" et "t + d t" | " L(t) = k > 1) &= mat(k ; 2) (mu d t + o(d t))^2 (1 - mu d t + o( d t))^(k-2)\
&= o(d t)$

*On pose $L(t)$ le nombre d'appels en cours, et on a: $(L(t), t >= 0)$ une CMTC de type processus de naissance et de mort.* (déjà dit)



#diagram(
  node-shape : circle,
  node-stroke : 0.1em,
  node((0,0), "0"),
  node((1,0), "1"),
  node((2,0), "2"),
  node((3,0), $dots$, stroke : 0em),
  node((4,0), $c$),
  node((5,0), $c+1$),

  edge((0,0), (1,0), bend: 20deg,"-|>", $lambda$),
  edge((1,0), (2,0), bend: 20deg,"-|>", $lambda$),
  edge((2,0), (3,0), bend: 20deg,"-|>", $lambda$),
  edge((4,0), (5,0), bend: 20deg,"-|>", $lambda$),

  edge((5,0),(4,0), bend: 20deg, $mu$, "-|>"),
  edge((3,0),(2,0), bend: 20deg, $mu$, "-|>"),
  edge((2,0),(1,0), bend: 20deg, $mu$, "-|>"),
  edge((1,0),(0,0), bend: 20deg, $mu$, "-|>"),
)

$lambda > 0 " et " mu>0$ 


La chaine est ergodique.

#grid(
  columns: 2,
  column-gutter: 10em,
  [#linebreak()
  $cases(lambda Pi_0 = mu Pi_1,
lambda Pi_1 = mu Pi_2,
"Donc par récurrence:"
lambda Pi_(c-1) = mu Pi_c,

    sum_(k=0)^(c) Pi_k = 1)$],
[
  $cases("En remplaçant" mu/lambda "par" rho: ,

Pi_0 = rho Pi_1,

Pi_1 = rho Pi_2,

"Donc par récurrence:"
 Pi_(c-1) = rho Pi_c,

Pi dot (1 + rho + rho^2/2! + dots + rho^c/c!) = 1)$]
)

#linebreak()


$Pi_0 = 1/(sum^c_(j=0) (rho^j)/(j!))$


$Pi_k = rho^k / k! / (sum_(j=0)^c (rho^j)/j!)$

$tau = Pi_c = (rho^c/c!) / (sum_(j = 0)^(c) rho^j/j!)$

*Première formule d'Erlang, ou Erlang-B*


$tau = X/lambda$ 


$tau = (lambda - Lambda)/lambda = 1 - Lambda/lambda$

$Lambda &= sum^c_(k = 0) k dot mu dot Pi_k\
&= mu dot sum_(k=0)^c k dot Pi_k\
&= mu dot E(L)$


$sum_(k=0)^(c) k dot Pi_k &= sum_(k=0)^(c) k dot rho^k/k! dot Pi_0\
&= rho sum_(k=0)^(c) rho^(k-1)/(k-1)! dot Pi_0\
&= rho sum_(k=0)^(c-1) rho^k/k! dot Pi_0 \
&= rho dot sum_(k=0)^(c-1) Pi_k \
&= rho dot (1 - Pi_c)$

On en déduit, en remplaçant dans $Lambda$:

$Lambda &= mu dot rho dot (1 - Pi_0)\
&= lambda dot (1 - Pi_c)$

D'où:

$tau &= 1 - Lambda/lambda \
&= 1 - (1 - Pi_c) \
&= Pi_c$

$E(L) = sum_(k=0)^(c) k^n Pi_k = rho dot ( 1 - Pi_c)$

#rem([$lim_(c -> infinity) Pi_c = 0 => lim_(c -> infinity) E(L) = rho$])

$E(R) = E(L)/Lambda = E(L)/(mu dot E(L)) = 1 / mu$

#underline[$E(R) = 1/mu$]

$E(R) = E(W) + E(S) = E(S) = 1/mu$, car $E(W) = 0.$

#grid(
  columns: 2, align: center,
  [#diagram(
  node-shape: circle,
  node-stroke : 0.1em,

  node((2,-1), $1$),
  node((2,1),$X$),
  node((2,-1.4),stroke : 0em),
  node((2,0.1 ), "c"),
  
  
  edge((0,0),(1,0),"-|>",$2 lambda$),
  edge((1,0),(1,1),"-|>"),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0),  label-side: right, label-pos:0%),
  edge((2.2,-1),(3,0), label-pos:0%),
  edge((3,0),(4,0),"-|>"),
  edge((2,-0.5),(2,-0.2), "dotted"),
  edge((2,0.4),(2,0.6), "dotted")
)], [$rho_N = (2 lambda) / (2 C mu) = lambda / (C mu)$]
)





#diagram(
  node-shape: circle,
  node-stroke : 0.1em,

  node((2,-1), $1$),
  node((2,1),$c$),
  
  
  edge((0,0),(1,0),"-|>",$lambda$),
  edge((1,0),(1,1),"-|>",$tau$),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0)),
  edge((2.2,-1),(3,0), $mu$, label-pos:0%),
  edge((3,0),(4,0),"-|>"),
  edge((2,0.1),(2,-0.1),"dotted")
)

$rho_N = lambda / (C mu)$

#diagram(
  node-shape: circle,
  node-stroke : 0.1em,

  node((2,-1), $1$),
  node((2,1),$c$),
  
  
  edge((0,0),(1,0),"-|>",$lambda$),
  edge((1,0),(1,1),"-|>",$tau$),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0),$mu$, label-side:right, label-pos:0%),
  edge((2.2,-1),(3,0)),
  edge((3,0),(4,0),"-|>"),
  edge((2,0.1),(2,-0.1),"dotted")
)



#underline[Pour le 1er système:]
#figure(
  image("images/graphe_exemple.jpg"),
)
$Pi_1 = 2 rho Pi_0$

$Pi_2 = rho Pi_1 = 2 rho^2 Pi_0$

Donc $tau_1 = (2 rho^2)/(1 + 2 rho + 2 rho^2)$

#underline[et Pour le 2e système:]

$Pi_1 = rho Pi_0$

$Pi_0 = 1 /(1+rho)$

Donc $tau_2 = rho / (1+rho)$

$tau_2-tau_1 = 1 /((1+p) (1+2 p + 2 p²))$

Or $(1+p) (1+2 p + 2 p²) = rho + 2 rho^2 + 2 rho^3 - 2 rho^3 > 0$. 

Donc $tau_2-tau_1 > 0$ ie : $tau_2 >tau_1$

Donc le 2e système a un plus grand taux de perte, et est donc moins efficace.

== Etude de la file M/M/C/C/N avec N > C



#diagram(
  node-shape: circle,
  node-stroke : 0.1em,

  node((2,-1), $1$),
  node((2,1),$N$),
  node((5,-1), $1$),
  node((5,1),$c$),
  node((0.25,1.75),$N$,stroke:0em),
  
  
  
  edge((0,0),(1,0)),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0),$mu$, label-side:right, label-pos:0%),
  edge((2.2,-1),(3,0),$mu$, label-pos:0%),
  edge((3,0),(4,0),"-|>"),
  edge((2,0.1),(2,-0.1),"dotted"),
  edge((4,0),(4.8,-1)),
  edge((4,0),(4.8,1)),
  edge((5.2,1),(6,0),$mu$, label-side:right, label-pos:0%),
  edge((5.2,-1),(6,0),$mu$, label-pos:0%),
  edge((5,0.1),(5,-0.1),"dotted"),
  edge((6,0),(7,0)),
  edge((7,0),(7,2)),
  edge((7,2),(0,2)),
  edge((0,2),(0,0)),
  edge((0.5,2),(0.5,1.5)),
  edge((0,1.5),(0.5,1.5)),
  edge((3.5,0),(3.5,2),"-|>", $tau$, label-side:left)
)

$rho = lambda/mu$



$L(t):$ nombre d'appels en cours à t.


$(L(t), t>= 0)$ est une CMTC de type processus de naissance et de mort.


=== Départ de la file:

$PP(1 "appel dépar entre" t  "et" t + d t | L(t)-k  > 0 ) = k mu d t + o(d t)$

$PP(0 "départ entre" t "et" t + d t | L(t) - k > 0) = 1 - k dot mu d t + o(d t)$


=== Arrivés de la file 


$PP(1& "arrivée entre" t "et" t + d t | L(t) - k) = (N - k) dot lambda d t + o(d t)\
 $

$PP(0 "arrivée entre" t "et" t + d t | L(t) - k) = 1 - (N - k) dot lambda d t + o(d t)$


*graph*
$mu > 0 "et" lambda > O$

Chaine ergodique


$Pi_1 = N rho Pi_0$

$Pi_2 &= N-1)/2 rho Pi_1 \
&= N(N-1) / 2 rho² Pi_0 \
&= binom(N,2) rho² Pi_0$




$Pi_c = (N-c+1)/c dot rho Pi_(c-1) = (N dot (N-1) dots (N-c+1))/c! dot rho^c Pi_0 = mat(N;c) dot rho^c dot Pi_0$

$Pi_0 = 1 / (sum_(j=0) ^c binom(N,j) p^j)$ ;

$Pi_k =( binom(N,k) rho ^k) / (sum_(j=0)^c binom(N,j) rho ^j) $


$tau != Pi_c$ 




#diagram(
  node-shape: circle,
  node-stroke : 0.1em,

  node((2,-1), $1$),
  node((2,1),$N$),
  node((5,-1), $1$),
  node((5,1),$c$),
  node((0.25,1.75),$N$,stroke:0em),
  node((3.2,0.2),$A$,stroke:0em),
  node((3.7,0.5),$X$,stroke:0em),
  
  
  edge((0,0),(1,0)),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0),$mu$, label-side:right, label-pos:0%),
  edge((2.2,-1),(3,0),$mu$, label-pos:0%),
  edge((3,0),(4,0),"-|>"),
  edge((2,0.1),(2,-0.1),"dotted"),
  edge((4,0),(4.8,-1)),
  edge((4,0),(4.8,1)),
  edge((5.2,1),(6,0),$mu$, label-side:right, label-pos:0%),
  edge((5.2,-1),(6,0),$mu$, label-pos:0%),
  edge((5,0.1),(5,-0.1),"dotted"),
  edge((6,0),(7,0)),
  edge((7,0),(7,2)),
  edge((7,2),(0,2)),
  edge((0,2),(0,0)),
  edge((0.5,2),(0.5,1.5)),
  edge((0,1.5),(0.5,1.5)),
  edge((3.5,0),(3.5,2),"-|>", $tau$, label-side:left),
)


$X = (N- c) lambda Pi_c$

$A = sum^c_(k = 0)_(k=0) (N-k) lambda dot Pi_k$

$tau &= X/A = (rho(N-c) cancel(lambda) Pi_c) / (sum_(k=0)^c (N_k) cancel(lambda) Pi_k) = (N-c) binom(N,c) rho^c cancel(Pi_0) / sum(k=0)^c (N-k) binom(N,k) rho^k cancel(Pi_0) \


&= (N-k) dot N!/((N-k)!k!) = N dot (N-1)!/((N-1-k)!k!) = N dot mat(N-1;k)$


$tau = (cancel(N) mat(N-1; c) rho^c)/(sum_k=0)^c cancel(N) (N-1;k) rho^k = Pi_c (N-1) < Pi_c(mu)$

= Chapitre 4 : Étu de file M/G/1

#diagram(
  node-shape : rect,
  node-stroke: 0.1em,

  node((1,0), " | | "),
  node((2,0), "X"),
  node((2,0.4), $b$,stroke:0em),

  edge((0,0),(1,0), $lambda$, "-|>"),
  edge((1,0),(2,0)),
  edge((2,0),(3,0), "-|>")
)

$E(S) &< + infinity #h(20mm) E(L) = ?\
E(S^2)&<  +infinity #h(20mm) E(R) = ?\
b &= "densité de probabilité du temps de service quelconque"\
rho &= lambda "E(S)"$

Arrivées Poissonniennes 1 serveurs taille population $infinity$

Temps de service quelconque FCFS capacité: $infinity$

$L(t):$ nombre de clients dans la file à instant t.

$(L(t),t>=0)$ est-il une CMTC? (comme la questtion est posée, c'est que non.)

=== Arrivées Poissonniennes:

$PP(1 "arrivée entre" t  "et" t + d t) =lambda d t + o(d t)$

$PP(0 "arrivée entre" t  "et" t + d t) =1 - lambda d t + o(d t)$



=== Départs Poissonniens:

$PP(1 "client en service en "t " termine se service entre" t  "et" t + d t) = "inconnu" $

Il faudrait connaitre la durée résiduelle de service à t:

#figure(
  image("images/20250318_115139.jpg",width:50%),
)
// si j'y pense je le referais au propre

$alpha(t):$ durée résiduelle de service à t.

$(L(t), alpha(t), t>=0)$ est un processus markovien


$alpha(t)$ à espace d'états continu.


== Méthode de la chaîne incluse:

On étudie le système à des instants particuliers (discrets) :

- Instants d'arrivée ;
- Instants de départs $-> alpha(t) = 0$ en ces points là.

C'est plus simple de regarder les instants de départ car on sait que le temps résiduel de service $alpha(t)= 0.$

=== Représentation des instants d'observations

$A_k(t) = PP(" 1 client arrivent à " t " trouve " k " clients dans la file") ->_(t-> infinity) a_k$

$d_k(t): PP( 1 "client partant à instant t laisse "k" clients dans la file.") ->_(t-> infinity) d_k$

$Pi_k(t) = PP(L(t)=k) ->_(t-> infinity) Pi_k$



#prop[*PASTA* (c'est pas une blague)


$forall k #h(2mm) forall t #h(5mm) A_k(t) = Pi_k (t)

=> forall k a_k=Pi_k$]


#prop[Si le système évolue par pas de +/- 1 : $forall k: a_k = d_k$]

//celui qui m'a mis un éléphant il se fait écraser par BABAR et toute sa famille
//HAHAHAAH
//???????


Pour un système qui évolue par pas de $plus.minus 1$

#table(
  columns: 3,
  [#text("#")],[arrivée],[départ],
  [1],[0],[1],
  [2],[1],[2],
  [3],[1],[1],
  [4],[2],[0]
)




$a_k^T:$ proportion de clients qui arrivent entre 0 et T et qui trouvent k clients dans la file.


$d_k^T :$ proportion de clients qui arrivent entre 0 et T et qui laissent k clients dans la file. Les plus simple à calculer.


si le système est vide à 0 et T, alors $forall k: a_k^T = d_k^T #h(5mm) "et donc" lim_(T -> infinity) a_k = d_k$

=>$forall$ *$k a_k = d_k = Pi_k$*


$q_n =$ nombre de clients dans la file quand le client $n$ part.

$v_n =$ nombre de clients qui arrivent pendant le service du client $n$.


$(q_n, n in NN)$ est une CMTD.

#demo[ On montre que $(q_n,n in NN)$ est une CMTD.
  
  
- $q_n = 0 #h(5em) q_(n+1) = v_(n+1)$
- $q_n>0 #h(5em) q_(n+1)=q_n-1+v_(n+1)$

$q_(n+1) = q_n - II_({q_n>0}) + v_(n+1)$

$PP(v_n = k ) = integral_(x=0)^(+infinity) PP(v_n = k | s_n = x)b(x) d x $

$s_n &= "temps de service du client" n\ $


$&= integral_(x=0)^(+infinity) (lambda dot x)^k/k! dot e^(-lambda k) d x = b_k$


=> $(q_n, n in NN)$ est 1 CMTD
]


$P = mat(b_0,b_1,b_2,b_3,dots;
b_0,b_1,b_2,b_3,dots;
,b_0,b_1,b_2,dots;
nothing
)$




$(1-b_0) dot d_0 = b_0 dot d_0$

$(1-b_0 - b_1) dot d_0 + (1-b_0 - b_1) dot d_1 = b_0 dot d_2$

On pourrait continuer les calculs.

Mais ce qui nous intéresse :

$ E(L) = sum_(k=0)^(+ infinity) k Pi_k = sum_(k=0)^(+ infinity) k d_k $



$q_(n+1) = q_n - II_({q_n>0}) + v_(n+1)\

q_n ->_(n -> +infinity) tilde(q)\ 

II_{q_n>0} ->_(n-> +infinity) II_{tilde(q)>0}\

v_n ->_(n -> infinity) tilde(v) \

E(tilde(q)) = ? = E(L)\

E(q_(n+1)) = E(q_n) - E(I_{q_n > 0}) + E(v_(n+1)) \

E(tilde(q)) = E(tilde(q))-E(1_{tilde(q)>0})+E(tilde(v))\

E(1_{tilde(q)>0}) = PP(tilde(q)>0) = E(tilde(v))
$

$PP(tilde(q) > 0 ) = 1 - d_0 = 1 - Pi_0 = U = Lambda E(S)$

$E(v_n) &= integral_(x=0) ^(+infinity) E(v_n|s_n = x)b(x) d x = lambda E(S)\
&= integral_(x=0)^(+infinity) lambda x b(x) dot d"x" \
&= lambda dot E(S)
$

$E(II_{tilde(q)> 0}) &= PP(tilde(q)>0) - E(tilde(v))\
&=lambda E(S) = Lambda dot E(S)\
&= rho

$

$q_(n+1)^2 = &q_n^2 + II_({q_(n_1)>0}) + n_(n+1)^2\
&- 2q_n dot cancel(II_({q_n>0})) + 2q_n v_(n+1)\
&- 2II_({q_n>0}) v_(n+1)$

$E(q_(n+1)^2) = &E(q_n^2) +E(II_{q_n>0})+E(v_(n+1)^2)\
&- 2E(q_n) + 2 E(q_n)E(v_(n+1))\
&-2E(II_{q_n>0})E(v_(n+1))$


$cancel(E(tilde(q)^2)) &= cancel(E(tilde(q)^2))+ E(1_{tilde(q)>0}) + E(tilde(v)^2) - 2 dot E(tilde(q)) + 2 dot E(tilde(v)) dot E(tilde(q)) - 2 dot E(1_({tilde(q)>0})) dot E(tilde(v))

$

$2E(tilde(q))(1-E(tilde(v))) = E(II_({tilde(q)>0})) - 2E(II_({tilde(q)>0}))E(tilde(v)) + (tilde(v)^2)$

$2E(tilde(q))(1-rho) = $*2*$ dot rho - 2 dot rho^2 + E(tilde(v))-$  *$E(tilde(v))$* 



*$ E(tilde(q)) = rho + (E(tilde(v) (tilde(v) - 1)))/(2 dot (1 - rho)) $*


$E(v_n (v_(n-1)) ) &= sum_(k=0)^infinity k(k-1)PP(v_n = k)\
&= sum_(k=0)^infinity k(k-1) integral_(x=0)^infinity PP(v_n = k | s_n = x) b(x) d"x" (lambda x )^k /k! \
&= integral_(x=0)^(+ infinity) e^(-lambda x) b(x) sum_(k=2)^infinity k(k-1) ((lambda x)^k)/(k!) d x\

&= integral_(x=0)^(+ infinity) e^(-lambda x) b(x) (lambda x) sum_(k=2)^infinity ((lambda x)^(k-2))/((k-2)!) d x\

&= integral_(x=0)^(+ infinity) cancel(e^(-lambda x)) b(x) (lambda x)^2 cancel(sum_(k=0)^infinity ((lambda x)^k)/(k!)) d x #h(3em) "car " sum_(k=0)^infinity ((lambda x)^k)/(k!) = e^(+ lambda x)\


 &= integral_(x = 0)^(+ infinity) lambda^2 dot x^2 dot b(x) d x\
&=lambda^2 dot E(S^2)$



*$E(L) = E(tilde(q)) = rho + (lambda^2 dot E(S^2))/(2 dot (1 - rho))$*



#demo([ *Première formule de Pollaczek–Khinchine*

  $C^2_S &= "Var"(s)/E(S)^2\
&= E(S^2)/E(S)^2 -1 
$

$E(S^2) = E(S)^2 dot (1 + C_S^2)

E(L_("M/G/1")) = rho + (lambda^2 dot E(S)^2 dot (1 + C_S^2))/(2 dot (1 - rho))$

*$ E(L_("M/G/1")) = rho + rho dot (1 + C_S^2))/(2 dot (1 - rho)) $*


Pour une charge $rho$ donnée, 
$E(L_(M"/"G"/"1))$ est une fonction croissante de $cal(C)^2_S$, donc minimale quand $cal(C)^2_S="Var"(S)=emptyset$

Pour une file M/D/1 $cal(C)^2_S = emptyset$


$E(L_("M/D/1")) &= rho + rho^2/(2 dot (1- rho))\
&= (rho dot (2 - rho))/(2 dot 1 - rho)$

$E(L_("M/M/1")) &= C_S^2 = 1\
&= rho + (cancel(2) dot rho^2)/(cancel(2) dot (1 - rho))\  
&= rho/(1 - rho)$







$E(R)= (E(L))/Lambda = (E(L))/lambda$

*$ E(R) = E(S) + (lambda E(S^2))/(2(1-rho)) $*

avec $(lambda E(S^2))/(2(1-rho) )= E(w)$ le temps moyen d'attente

])



== Autre méthode



#diagram(
  node-shape : rect,
  node-stroke: 0.1em,

  node((1,0), " | | "),
  node((2,0), "X"),
  node((2,-0.4), $theta$,stroke:0em),
  node((1,-0.5), $beta_n$,stroke:0em),

  edge((0,0),(1,0), "-|>"),
  edge((1,0),(2,0)),
  edge((2,0),(3,0), "-|>"),
  edge((0.7, -0.3),(1.3, -0.3), "<|-|>")
)

$w_n = $ temps d'attente du client $n$

$theta_n = $ temps résiduel de service quand $n$ arrive 

$beta_n =$ nombre de clients en train d'attendre quand $n$ arrive.

$s_k =$ temps de service du client $k$


$w_n = theta_n + sum^(n-1)_(k=n dot beta_n) s_k$

$E(w_n) = E(theta_n) + E(beta_n) dot E(S)$

On applique: $lim_( n-> infinity)$
- On applique aussi *PASTA* sur $theta_n "et" beta_n$

$E(w) = E(theta) + E(L_w) dot E(S)$

Avec $E(theta):$ temps moyen résiduel en régime permanent.

et $E(L_w)$: nombre myen de clients en train d'attendre en régime permanent

$E(w) = E(theta) + E(L_w) dot E(S)$
$E(theta) =$ tps moyen résiduel en régime permanent

$E(L_w) = $ nombre moyen de clients en train d'attendre en régime permanent

#diagram(
  node-shape : rect,
  node-stroke: 0.1em,

  node((1,0), " | | "),
  node((2,0), "X"),
  node((2,-0.4), $theta$,stroke:0em),
  node((1,-0.5), $beta_n$,stroke:0em),

  edge((0,0),(1,0), "-|>", $lambda$),
  edge((1,0),(2,0), $Lambda_w$),
  edge((2,0),(3,0), "-|>", $Lambda$),
  edge((0.7, -0.3),(1.3, -0.3), "<|-|>")
)

On a donc: 

$E(L_w) &= Lambda_w E(w) "d'après la loi de Little."\
&= lambda E(w)$

$E(w) {1 - lambda E(S)} = E(theta)$

*$ E(w) = E(theta)/(1- rho) $*




$M_T:$ nombre de clients servis entre 0 et T.

$overline(theta_T) &= 1/T integral_(t=0)^T alpha(t) d t\
&= M_T/T dot 1/M_T dot sum_(k=1)^M_T s_k^2/2 \
&= 1/2 (M_T)/T 1/(M_T) sum^(M_T)_(k=1) s_k^2\

&arrow.b T->infinity\
&E(Theta)= 1/2 dot Gamma dot E(S^2) = 1/2 dot lambda dot E(S^2)$

*$ E(w) = (lambda dot E(S^2))/(2(1-rho)) $*

= Réseaux de files d'attente
// Chapitre 5 mais on est à 7 OKLM
// pourquoi d'un coup il decide de numéroter les chapitre ??????
// Bonne question
// c'est qu'on a une intro et un chapitre annexe ou quoi
// mais c chiant
// Nos parties 4-5 ont pas l'air dêtre des chapitres
// Je suis allé voir les titres et ai essayé de mieux les mettre, donc là on a bien 5 chapitres et 1 intro

#def([*Réseau de files d'attente*
  
  Un réseau de files d'attentes est composé d'un certain nombre de files d'attente simples et de clients qui circulent entre ces files.
  
  - On suppose que le passage d'une file à un autre est instantanée. 

  - On suppose qu'un client n'est que dans 1 file à la fois et qu'un serveur ne sert qu'un client à la fois.

  - On appelle le cheminement des clients dans le réseau "routage" (#emoji.motorway #emoji.person.old). Ce routage peut être déterministe, aléatoire, adaptatif etc...
  - on va distinguer les réseaux de files d'attente ouverts dans lesquels des clients rentrent dans le réseau, circulent entre les files et ressortent des réseaux de files d'attente fermés où un nombre constants de clients circulent entre les files.

])

_Exemple: de réseaus fermés_


#diagram(
  node-shape: circle,
  node-stroke : 0.1em,

  node((2,-1), $1$),
  node((2,1),$N$),
  node((5,-1), $1$),
  node((5,1),$c$),
  node((0.25,1.75),$N$,stroke:0em),
  
  
  edge((0,0),(1,0)),
  edge((1,0),(1.8,-1)),
  edge((1,0),(1.8,1)),
  edge((2.2,1),(3,0)),
  edge((2.2,-1),(3,0),$lambda$, label-pos:0%),
  edge((3,0),(4,0),"-|>"),
  edge((2,0.1),(2,-0.1),"dotted"),
  edge((4,0),(4.8,-1)),
  edge((4,0),(4.8,1)),
  edge((5.2,1),(6,0)),
  edge((5.2,-1),(6,0),$mu$, label-pos:0%),
  edge((5,0.1),(5,-0.1),"dotted"),
  edge((6,0),(7,0)),
  edge((7,0),(7,2)),
  edge((7,2),(0,2)),
  edge((0,2),(0,0)),
  edge((0.5,2),(0.5,1.5)),
  edge((0,1.5),(0.5,1.5)),
  edge((3.5,0),(3.5,2),"-|>"),
)

#diagram(
  node-shape : rect,
  node-stroke: 0.1em,

  node((0,0), $| |$),
  node((3,0), $| |$),
  node((3.5,0), $X$),

  node((3,1), $X $),
  node((3.5,1), $| |$),
  node((2.2,0.8),$N$, stroke:0em),

  edge((3,0),(3.5,0),),
  edge((3.5,0), (5,0)),
  edge((5,0),(5,1)),
  edge((5,1),(3.5,1), "-|>"),
  edge((3.5,1),(3,1)),
  edge((0,0),(1,0)),
  edge((1,0),(2,-0.5)),
  edge((2,0),(3,0)),
  edge((2,0),(2,1), $*$),
  edge((1,1),(3,1),"<|-"),
  edge((2.4,1),(2.4,0.6)),
  edge((2,0.6),(2.4,0.6))
  
)




== Réseaux de files d'attente

#def([*Réseau de capacité maximale du système (y compris les clients en service et en attente).*

Un réseau #underline[ouvert] avec K files d'attentes est dit *réseau de Jackson* si:
- Les arrivées dans le réseau sont poissonniennes de taux $lambda$
- chaque file:
  - 1 serveur ;
  - FCFS ;
  - service exponentiel de taux $mu_i$ ;
  - capacité $infinity$.

- Routage probabiliste:
  - $p_"ij"$: proba qu'en sortant de la file i, le client aille dans la file j ;
  - $P= (p_"ij")_(1<i<K)^(1<j<K)$ la matrice de routage
    
  La matrice P est *sous-stochastique*.

  - $p_"i0"$: la probabilité qu'en sortant de la file i, le client quitte le réseau.
  - $p_"0i"$: la probabilité qu'en rentrant, le client aille vers la file i
  - $q_0 = (p_01,dots,p_(0k))$
])

=== Flux dans les réseaux de Jackson
$lambda_i$: débit d'entrée de la file $i$

$Lambda_i$ = débit de sortie de la file $i$

On en déduit la relation entre les 2:

$ lambda_i = lambda dot p_"Oi" + sum_(j=1)^K Lambda_j dot p_"ji" $
$ lambda: "taux d'arrivée poissonnienne" $

$e_i$ = nombre moyen de passages d'un client par la file $i$

$e = (e_j,dots,e_k)$



Si le réseau est stable :
$lambda_i &= Lambda_i$

$lambda_i &= lambda dot p_(0i) + sum_(j-1)^k lambda_j p_"ij" \

lambda_i &= lambda e_i\

lambda e_i &= lambda dot p_(0i) + sum_(j=1)^k lambda e_j p_"ji"\

e_i &= p_(0i) + sum^K_(j=1) e_j p_(i j)$

$e = q_0 + e dot P$

On isole $q_0$:

$e(II - P) = q_0$

- Donc si la matrice I - P est inversible:

$e = q_0 dot (I - P)^(-1)$

Si la matrice I - P n'est pas inversible, cela se traduit par une possibilité de ne jamais sortir du réseau.

_exemple 1 :_

#diagram(
  node-shape: rect,
  node((0,0), $lambda$),
  node((1.5,0), $ | | $, stroke : 0.1em),
  node((2.5,0), $X$, stroke : 0.1em),

  edge((0,0),(1.5,0),"-|>"),
  edge((1.5,0),(2.5,0)),
  edge((2.5,0),(3.5,0),$1-p$, "-|>", label-side : right, label-pos : 80%),
  edge((3,0),(3,-0.5)),
  edge((3,-0.5),(1,-0.5)),
  edge((1,-0.5),(1,0), "-|>", $p$),
  
)

On voit simplement que: $e_1 = 1 + p dot e_1$ Si: $1-p > 0$

donc: $e_1 = 1/(1-p)$

On note: $NN_1:$ le nombre de passages dans la file 1.

On a alors:

$PP(N_1 = 1) = 1 - p$

$PP(N_1 = 2) = p dot (1 - p)$

$PP(N_1 = k) = p^(k-1) dot (1 - p)$

On remarque une loi géométrique. Et donc comme:
$EE(NN_1) = sum_(k= 0)^(infinity)PP(NN_1 = k)$.

La somme géométrique nous donne:

*$ EE(NN_1) = 1/(1-p) $*




_exemple 2:_

#diagram(
  node-shape: rect,
  node-stroke:0.1em,
  node((0,0),$| |$),
  node((0.5,0),$X$),
  node((0.5,-0.5),$mu_1$,stroke:0em),

  node((2.5,-1), $| |$),
  node((3,-1), $X$),
  node((3,-1.5),$mu_2$,stroke:0em),

  node((2.5,1), $| |$),
  node((3,1), $X$),
  node((3,0.5),$mu_3$,stroke:0em),

  edge((0,0),(0.5,0)),
  edge((2.5,-1),(3,-1)),
  edge((2.5,1),(3,1)),

  edge((-2,0),(0,0), "-|>", $lambda$, label-pos:20%),
  edge((0.5,0),(1.5,0)),
  edge((1.5,0),(1.5,-1)),
  edge((1.5,0),(1.5,1)),
  edge((1.5,-1),(2.5,-1), "-|>", $1/2$),
  edge((1.5,1),(2.5,1), "-|>", $1/3$),
  edge((3,-1),(4,-1)),
  edge((4,-1),(4,0)),
  edge((3,1),(4,1)),
  edge((4,1),(4,0)),
  edge((4,0),(5,0)),
  edge((5,0),(5,-2)),
  edge((5,-2),(-1,-2),"-|>"),
  edge((-1,-2),(-1,0), "-|>"),
  edge((1,0),(1,2),"-|>", $1/6$)
)


On a:

$q_0 = (1 0 0)$

$P = mat(1, 1/2, 1/3; 1, 0, 0; 1, 0, 0)$





#grid(
  columns: 2,
  column-gutter: 10em,
  [#linebreak()
  $cases("On tire de cette matrice:",
e_1 = 1 + e_2 + e_3,
e_2 = 1/2 dot e_1,
e_3 = 1/3 dot e_1)$],
[$cases("On remplace dans les différentes équations":,
e_1 = 6,
e_2 = 3,
e_3 = 2)$]
)

$L_j(t)$: nombre de clients dans la file j à t.

$(L_j(t), t>= 0)$ est-il une CMTC? 

- $PP("1 arrivée de l'extérieur dants la file j entre t et" t+d t )=lambda dot "dt" +o dot ("dt")$

- $PP("1 fin de service entre t et" t+d t)=mu dot "dt" +o dot ("dt")$

- $PP("1 arrivée d'1 autre file entre t et" t+d t " "(L_j(t)=n_j))=??$

$((L_1(t),...,L_K(t)) t>=0) "est un CMTC"$

Si un client passe de la file i à la file j:

$PP(L_j(t + d t) = n_1, dots , L_j(t + d t) = n_j + 1, dots, L_i(t + d t) = n_i - 1, L_k(t + d t) = n_k | L_1(t) = n_1, L_j(t) = n_j), L_i(t) = n_i, L_k(t) = n_k) = p_"ij" mu_i d t + o(d t)$ 

Ce n'est pas un processus de naissance et de mort.

#underline[Notations :] 

$n = (n_1,dots,n_k)\
n_j = (n_1,dots,n_(j+1),dots,n_k)\
n_i = (n_1,dots,n_(i-1),dots,n_k)\
n_i+j = (n_1,dots,n_(i+1),dots,n_(j-1),dots,n_k)
$

#theo([Théorème de Jackson

Dans un réseau de Jackson ouvert si :
- $rho_j = lambda_c_j/mu_j < 1 #h(10mm) 1<=j<=k$
- $Pi(n) = Pi_(j=1)^k (1-p_j)p_j^n_j #h(10mm)$ solution à forme produit
])

#demo[
  #linebreak()
  $sum_(n in Omega) Pi(n)$

  $Omega = {(n_1, dots, n_K), n_1 >= 0, dots, n_K>=0}$

  $sum_(n_1 =0)^infinity sum_(n_2 =0)^infinity dots sum_(n_K =0)^infinity Pi_(j=1)^K (1- rho_j)e_j^(n_j) =1$

+ On va vérifier que $Pi$ satisfait le système linéaire $Pi dot Q = 0:$

  $forall n in Omega\
  Pi(n) {lambda + sum^K_(j=1) mu_j II_({n_j>0})} = &sum^K_(j=1) mu_j p_(j 0) Pi(n_(j^+)) \
  &+ sum_(j=1)^k lambda dot p_(0j) II_{n_j>0}Pi(n_j)\
  &+ sum_(i = 1)^K sum_(j=1)^K mu_i p_"ij" II_({n_j > 0}) dot Pi(n_(i^+j^-))
  $

  *Équation de Chapman-Kolmogorov* ou *Équation d'équilibre globale*


+ On va vérifier que $Pi$ satisfait toutes les équations d'équilibre globale

  On va écrire à partir de l'équation globale ($K+1$) équation dites d'équilibre local.


  (0) $lambda dot Pi(n) =^? sum^K_(j = 1) mu_j p_"j0" dot Pi(n_(j^+))$
  
  (1)-($K$) $mu_j II_{n_j > 0} Pi(n) =^? lambda dot p_(0j) II_{n_j>0} Pi(n_j^-) + sum_(i=1)^k mu_i dot p_"ij" II_{n_j>0} Pi_n_((i+j))^-$

  L'équation (1)-($K$) est plus facile à prouver (contre intuitif), donc on commence par prouver celle-ci:

  - (1)-($k$): 
    - Si $n_j = 0$, alors tout de suite on a: 0 = 0.
    - $"Si" n_j != 0, "alors" mu_j Pi(n) &=^? lambda p_(0 j) Pi(n_(j^-)) + sum^K_(i=1) mu_i p_(i j) Pi_(n^+ j^-) \
    cancel(mu_j) cancel(Pi(n)) &=^?cancel( lambda) p_(0 j) cancel(Pi(n)) cancel(mu_j)/(cancel(lambda) e_j) + sum^K_(i=1) cancel(mu_i) p_(i j) cancel(Pi(n)) (cancel(lambda) e_i)/cancel(mu_i) cancel(mu_i)/(cancel(lambda) e_j)\
    e_j &=^? p_(0 j) + sum^K_(i=1) p_(i j) e_i
$

On démontre maintenant l'autre équation:
  - (0)
  
  $lambda dot Pi(n) &=^? sum_(j = 1)^K mu_j p_"j0" Pi(n_j^+)\
  &=^? sum_(j= 1)^K mu_j dot lambda_"j0" dot Pi(n) dot (lambda_e_j)/mu_j$

  On simplifie par $lambda dot Pi(n)$ des 2 cotés, ce qui nous donne:

  *$ 1 =^? sum_(j=1)^K e_j p_"i0" $*

On reprends le résultat de (1) - (K) et on va développer jusqu'à arriver au résultat de (0):
  
$e_j = p_(0j) + sum_(i=1)^k p_"ij" e_i$



$sum_(j=1)^k e_j &= sum_(j=1)^k p_(0j) + sum_(j=1)^k sum_(i=1)^k p_"ij" e_i\
&= 1 + sum_(j=1)^k sum_(i=1)^k p_"ij" c_j = 1 + sum_(j=1)^k sum_(i=1)^k p_"ji" e_j$

$sum_(j=1)^k e_j(1 - sum_(i=1)^k p_"ij") = 1\
sum_(j=1)^k = e_j p_(j emptyset) =1$



Donc $Pi$ satisfait toutes les équations d'équilibre local:
- $=>$ toutes les équations d'équilibre local
- $=>$ c'est la solution de: $cases(Pi dot Q = 0, |M| = 1)$

]

#cor[dans un réseau de Jackson (si $p_j < 1 " ; " 1<=j<=K$) chaque file se comporte comme une file M/M/1 de taux d'arrivée $lambda e_i$ et taux de service $mu_i$ (chaque $rho_j$)

#grid(
  columns: 2,
  column-gutter: 5em,
  [$E(L_j) = rho_j/(1-rho_j)$

$E(L) = sum^K_(j=1) E(L_j)$],
[$E(R_j) = 1/(mu_j - lambda e_j)$

$E(R)=(E(L))/lambda = sum^K_(j=1)e_j E(R_j)$]
)]

$Pi_j(n_j) = sum_(n_1 = 0)^infinity sum_(n_2 = 0)^infinity dots sum_(n_(j-1) = 0)^infinity sum_(n_(j+1) = 0)^infinity dots sum_(n_K = 0)^infinity Pi_(i = 2)^K (1-p_i)^(n_i) dot p_i$


#diagram(
  node-shape: rect,
  node((1.5,0), $ | | $, stroke : 0.1em),
  node((2.5,0), $X$, stroke : 0.1em),
  node((2.5,0.3), $mu$, stroke:0em),

  edge((0,0),(1.5,0),"-|>", $lambda$, label-pos:20%),
  edge((1.5,0),(2.5,0)),
  edge((2.5,0),(3.5,0),$(1-p)$, "-|>", label-side : right, label-pos : 80%),
  edge((3,0),(3,-0.5),$p$),
  edge((3,-0.5),(1,-0.5)),
  edge((1,-0.5),(1,0), "-|>"),
  edge((1,-0.5), (0,-0.5))
  
)

$e_1 = 1/(1-p)$

$rho_1 = (lambda dot e_1) / mu <1 => E(L_1) = (lambda dot e_1/mu)/(1-lambda dot e_1/mu)\
E(L) = E(L_1) = (lambda/(mu(1-p)))/(1 - lambda/mu(1-p))$

$E(R_1) = 1/(mu-lambda e_1) = 1/(mu - lambda/(1-p))$

$E(R) = e_1 E(R_1) = 1/(mu(1-p)-lambda)$

$L_1(t)$ est 1 CMTC. 

#diagram(
  node-shape : circle,
  node-stroke : 0.1em,
  node((0,0), "0"),
  node((1,0), "1"),
  node((2,0), "2"),
  node((3,0),"3"),
  node((4,0),$dots$, stroke:0em),

  edge((0,0), (1,0), bend: 20deg,"-|>", $lambda$),
  edge((1,0), (2,0), bend: 20deg,"-|>", $lambda$),
  edge((2,0), (3,0), bend: 20deg,"-|>", $lambda$),
  edge((3,0), (4,0), bend: 20deg,"-|>", $lambda$),

  edge((3,0),(2,0), bend: 20deg, $mu(1-p)$, "-|>"),
  edge((2,0),(1,0), bend: 20deg, $mu(1-p)$, "-|>"),
  edge((1,0),(0,0), bend: 20deg, $mu(1-p)$, "-|>"),
  edge((4,0),(3,0), bend: 20deg, $mu(1-p)$, "-|>"),
  
)


C'est la même chaine que pour 1 file M/M/1 de taux d'arrivée $lambda$ et de taux de service $mu(1-p)$.

D'où: $E(L) = rho/(1-rho) = (lambda)/(mu dot (1-rho))/(1 - lambda/(mu dot (1 - p)))$

Et donc:

*$ E(R) = 1/(mu dot (1-p) - lambda) $*

#pagebreak()

_exemple 2:_

On reprends l'exemple 2 fait précédemment:

#diagram(
  node-shape: rect,
  node-stroke:0.1em,
  node((0,0),$| |$),
  node((0.5,0),$X$),
  node((0.5,-0.5),$mu_1=1$,stroke:0em),

  node((2.5,-1), $| |$),
  node((3,-1), $X$),
  node((3,-1.5),$mu_2=1$,stroke:0em),

  node((2.5,1), $| |$),
  node((3,1), $X$),
  node((3,0.5),$mu_3=2/3$,stroke:0em),

  edge((0,0),(0.5,0)),
  edge((2.5,-1),(3,-1)),
  edge((2.5,1),(3,1)),

  edge((-2,0),(0,0), "-|>", $lambda = 1/12$, label-pos:20%),
  edge((0.5,0),(1.5,0)),
  edge((1.5,0),(1.5,-1)),
  edge((1.5,0),(1.5,1)),
  edge((1.5,-1),(2.5,-1), "-|>", $1/2$),
  edge((1.5,1),(2.5,1), "-|>", $1/3$),
  edge((3,-1),(4,-1)),
  edge((4,-1),(4,0)),
  edge((3,1),(4,1)),
  edge((4,1),(4,0)),
  edge((4,0),(5,0)),
  edge((5,0),(5,-2)),
  edge((5,-2),(-1,-2),"-|>"),
  edge((-1,-2),(-1,0), "-|>"),
  edge((1,0),(1,2),"-|>", $1/6$)
)

On en tire :
$cases(e_1 = 6, e_2 = 3, e_3 = 2)$

Ainsi que les équations des différents $rho$:
$cases(
  rho_1 = (lambda e_1)/mu_1 = (1/12 times 6)/1 = 1/2 < 1,
  rho_2 = (lambda e_2)/mu_2 = (1/12 times 3)/1 = 1/4 < 1,
  rho_3 = (lambda e_3)/mu_3 = (1/12 times 2)/(2/3) = 1/4 < 1,
)$

$E(L_1) = rho_1/(1-rho_1) = (1/2)/(1-1/2) = 1$

$E(L_2) = rho_2/(1-rho_2) = (1/4)/(1-1/4) = 1/3$

$E(L_3) = rho_3/(1-rho_3) = (1/4)/(1-1/4) = 1/3$

$E(L) = 5/3$

$E(R) = (5/3)/(1/12) = 20$

$E(R_1) = (E(L_1))/(e_1 lambda)= 1/(1/12 times 6) = 2$

$E(R_2) = (1/3)/(3 dot (1/12)) = 12/9 = 4/3$


$E(R_3) = (E(L_3))/(e_3 lambda)= (1/3)/(1/12 times 2) = 2$



=== Réseaux de Jackson fermés 
#def[*Réseaux de Jackson fermés* :

Un réseau de file d'attente fermé comportant $K$ files et $M$ clients sera dit réseau de Jackson fermé si :
- chaque file :
  - 1 serveur ;
  - FCFS ;
  - Service exponentiel de taux $mu_i$ ;
  - Capacité $infinity$ (au - $M$).


- Routage probabiliste:
  
  $p_"ij"$: proba qu'en sortant de la file i, le client aille dans la file j 

    $P$ matrice de routage $P=(p_(i j))$ est *stochastique*.


- Flux dans le réseau:
  
  $lambda_j &= sum_(i = 1)^K Lambda_i dot p_"ij"\
  &=  sum_(i = 1)^K lambda_i dot p_"ij" $

  $e_j$ = nombre moyen de passage d'un client par la file $j$.

  $lambda_j = lambda e_j$ #h(10mm) $e=(e_1, dots , e_K)$

  $e_j = sum^K_(i=1) e_i p_(i j)$



  $e = e dot P$
  
  Donc en passant de l'autre coté de l'égalité:

  $e(I - P) = 0$, La matrice I - P n'est pas inversible.

  La notion de nombre moyen de passages n'est plus qu'une solution relative.


- à un temps d'observation T, $e_j (T) = $ nombre moyen de passage par j pendant $T$

- #diagram(
  node-shape:rect,
  node-stroke:0.1em,

  node((0,0), $| |$),
  node((0.5, 0), $X$),
  node((0,1), $X$),
  node((0.5, 1), $| |$),

  edge((0,0),(0.5,0)),
  edge((0,1),(0.5,1)),
  edge((0,0),(-1,0)),
)


par rapport à 1 point d'observation
- $e_j^* :$ nombre moyen de passages par j entre 2 passages au point d'observation.

$ ."Les critères de performance seront alors *relatifs* à ce point.". $
]



$e^* = e^* P + 1 $ équation liée au point d'observation

$L_i(t):$ nombre de clients dans la file à t.

$(L_i (t), t>=0) $ est il un CMTC ?

$PP(1 "départ entre t et t+dt |" L_i (t) = n_i > 0) = mu_i dot "dt" + "o(dt)" $

$PP(1 "arrivéé") = ??$ (inconnu)

$((L_1(t), dots, L_k(t)), i>=0)$ est 1 CMTC

$n = (n_1,dots,n_k)$

$PP(L_i (t+d t) = n_1,dots,L_i (t + d t) = n_i - 1), dots, L_i (t + d t) - n_j +1 dots | cases(L_1 (t) = n_1 - L_i (t) -n_i >0, L_k (t) = n_k) $

Ce n'est pas un processus de naissance et de mort. 

$n=(n_1 dots n_K), " " n_(i^+j^-) = (n_1, dots, n-i+1,dots,n_j-1,dots,n_K)$


$Omega = {n = (n_1,...,n_k) |  n_1 + n_2 +...+ n_k = M "et" 0 <= n_j <= M forall j}$

 $ abs(Omega)  = binom(M+K-1, K-1) = binom(M+K-1, M)$

#theo[*Théorème de Gordon et Newell* On envisage un modèle fermé dans lequel on a en permanence N clients
#linebreak()
Dans un réseau de Jackson fermé si le graphe formé par les fils est fortement connexe

$Pi (n) = G dot Pi_(j=1)^k (e_j^"*"/mu_j)^(n_j)$
#h(10mm)$G "/" Sigma_(n in Omega) Pi(n)=1$

Solution à forme produit
]
#demo[ *Démonstration du Théorème de Gordon et Newell*

On va vérifier que $Pi$ satisfait $Pi dot Q= 0$

On écrit les équations de Chapmann-Kolmogorov

  $Pi(n)= Sigma_(j=1)^k II{n_j>0} mu_j = Sigma_(i=1)^k Sigma_(j=1)^k mu_i dot "p"_"ij" dot II{n_j>0} dot pi_(n_i + j^-) 
$

On écrit les équations d'équilibre local

$(1)-(K) " " Pi(n)mu_j II_({n_j>0})=sum^K_(i=1)mu_i II_({n_j>0})p_(i j) Pi_(n_(i^+ j^-))$

soit :
- $n_j= 0 => 0 = 0 $
- $n_j >0  => Pi(n) mu^1_j &= sum_(i=1)^k  mu_i dot p_(i j)dot  Pi(n) dot  e_i^"*"/mu_i dot mu_j/e_j^"*"\
&e_j^* =^? sum_(i=1)^k p_(i j) dot e_i^* $

*Algorithme de mise en oeuvre*
- on fixe un point d'observation ;
- $e^* = e^* P$ on passe une seule fois par le point d'observation ;
- on décrit l'espace d'état et on écrit les probabilités des états en fonction de $G$ ;
- on détermine $G$
- on choisit une file $i$ et on détermine son taux d'occupation de serveur: 

$U_i &= sum_(n in Omega n_i>0) Pi(n) \

  &= Lambda_i dot E(S_i) = Lambda_i / mu_i = (Lambda^* dot e_i^*)/ mu_i  
$
 $Lambda^"*"$ débit au point d'observation.

 $Lambda_i = Lambda^* e_i^*\
 Lambda^* = (U_i mu_i)/(e_i^*)$
  
$overline(R^*) = M / Lambda^* $
] 


#diagram(
  node-shape: rect,
  node-stroke:0.1em,
  node((0,0),$| |$),
  node((0.5,0),$X$),
  node((0.5,-0.5),$mu_1=1$,stroke:0em),

  node((2.5,-1), $| |$),
  node((3,-1), $X$),
  node((3,-1.5),$mu_2=1$,stroke:0em),

  node((2.5,1), $| |$),
  node((3,1), $X$),
  node((3,0.5),$mu_3=2/3$,stroke:0em),

  node((-1.7,1.7),$M=2$, stroke:0em),

  node((3.5,-1),"X",stroke:0em),

  edge((0,0),(0.5,0)),
  edge((2.5,-1),(3,-1)),
  edge((2.5,1),(3,1)),

  edge((-2,0),(0,0), "-|>", $lambda = 1/12$, label-pos:20%),
  edge((0.5,0),(1.5,0)),
  edge((1.5,0),(1.5,-1)),
  edge((1.5,0),(1.5,1)),
  edge((1.5,-1),(2.5,-1), "-|>", $1/2$),
  edge((1.5,1),(2.5,1), "-|>", $1/3$),
  edge((3,-1),(4,-1)),
  edge((4,-1),(4,0)),
  edge((3,1),(4,1)),
  edge((4,1),(4,0)),
  edge((4,0),(5,0)),
  edge((5,0),(5,-2)),
  edge((5,-2),(-1,-2),"-|>"),
  edge((-1,-2),(-1,0), "-|>"),
  edge((1,0),(1,2),"-|>", $1/6$ ),
  edge((1,2),(-2,2)),
  edge((-2,2),(-2,0)),
  edge((-2,1.5),(-1.3,1.5)),
  edge((-1.3,1.5),(-1.3,2))
  
)




$ P = mat(1/6, 1/2,  1/3 ; 1 , 0, 0 ; 1, 0,0) $

#grid(
  columns: 2, column-gutter: 10mm,
  [$e_1 = 1/6 dot e_1 + e_2 + e_3\

e_2 = 1/2 dot e_1\

e_3 = 1/3 dot e_1$],[
  #linebreak() 
$=> e_1^* = 2\
e_3^* = 2/3$]
)

#grid(
  columns: 3, column-gutter: 30mm,
  [$(e_1^*)/(mu_1) = 2$], [$(e_2^*)/mu_2 = 1$], [$(e_3^*)/mu_3 = 1$]
)
#v(5mm)
$Pi(2#h(3mm) 0#h(3mm) 0) = G #h(3mm)2^2#h(3mm)0^1#h(3mm) 0¹ = 4 G = 4/11\
Pi(1#h(3mm) 1#h(3mm) 0) = G #h(3mm)2^1#h(3mm)0^1#h(3mm) 0^0 = 2G = 2/11\
Pi(1#h(3mm) 0#h(3mm) 1) = G #h(3mm)2^1#h(3mm)0^0#h(3mm) 0^1 = 2G = 2/11\
Pi(0#h(3mm) 2#h(3mm) 0) = G =1/11\
Pi(0#h(3mm) 1#h(3mm) 1) = G = 1/11\
Pi(0#h(3mm) 0#h(3mm) 2) = G =1/11$


$G=1/11$

Je choisis la file 2:

$U_2 = Pi(1#h(3mm) 1#h(3mm) 0) + Pi(0#h(3mm) 2#h(3mm) 0) + Pi(0#h(3mm) 1#h(3mm) 1) = 4/11$

$Lambda^* = (U_2 dot mu_2)/e_2^* = 4/11$


Si on avait pris la file 1 : 

$U = Pi (2#h(3mm) 0#h(3mm) 0) + Pi (1#h(3mm) 1#h(3mm) 0) + Pi (1#h(3mm) 0#h(3mm) 1) = 8 / 11 $

$Lambda^* = (U_1 mu_1)/(e_1^*) = (8/11 times 1)/2=4/11$

$overline(R^*)= 2/(4/11) = 11/2$

$e_1^+ = 6\
e_2^+ = 3\
e_3^+ = 2$

Les probabilités stationnaires sont identiques. 

$U_i$ également.

$Lambda^* = (U_2 dot mu_2)/e_2^* = 4/11/3 = 4/33$

$(lambda,mu_i,P,q_0) ->^"Jackson" cases(E(L_i),E(L)) ->^"Little" cases(E(R_i),E(R))$

$(mu_i, P, M) ->^"Th de Gordon & Newell"  Lambda^* -> ^"Little" E(R^*) $



*Récurrence Mean Value Analysis (MVA)*
(Algorithme de Reiser)

Dans un réseau de Jackson fermé on note 
- $overline(R_i)(M)$ le temps moyen de réponse de la file $i$ quand il y a $M$ clients en régime permanent;
- $overline(L_i)(M)$ le nombre moyen de réponses quand il y a M clients en régime permanent;
- $overline(S_i)$ le temps moyen de service;
- $overline(Q_i) (M)$ le nombre moyen de clients dans la file i en régime permanent quand un client arrive;

$overline(R_i) (M) &= overline(Q_i)(M) dot overline(S)_i+overline(S)_i\
&= (1+overline(Q_i)(M)) 1/mu_i$


#diagram(
  node-stroke:0.1em,
  node-shape : rect,

  node((0,0),$| |$),
  node((1,0),$X$),
  node((1,0.3),$mu_i$, stroke:0em),

  edge((-1,0),(0,0), "-|>"),
  edge((0,0),(1,0)),
  edge((1,0),(2,0),"-|>"),

  edge((-0.3,0.6),(1.3,0.6),"<|-|>")
)

#theo[*Théorème de Sevak-Mitrni (et non Mittérand, le poisson président des neuils)* 

Dans un réseau de Jackson fermé:
  
$overline(Q_i)(M) = overline(L_i)(M-1)$

$e_i^* dot overline(R_i) (M) = (1+ overline(L_i) (M)) 1/mu_i dot e_i^*$
]

*Récurrence MVA* : 
#algorithm(import algorithmic: *,
  For(cond : $j "from" 1 "to" k$, {$C_j <- emptyset$}),
  State[*end for*]
  
)


#pagebreak()
#algorithm(
  For(cond : $i "from" 1 "to" M$,{
    For(cond : $j "from" 1 "to" k$,{
      $e_j^* overline(R_j) = (1 + overline(L_j) dot (i dot e_j^*)/mu_j)$
    })
    State[*end for*]
    Assign[$e_j^* overline(R_j)$][$(1 + overline(L_j) dot (i dot e_j^*)/mu_j)$]
    Assign[$Lambda^*$][$i/overline(R)$ (Little global)]

    For(cond : $j "from" 1 "to" k$,{
      Assign[$L_j$][$Lambda^* dot e_j^* overline(R_j)$]
    })
    State[*end for*]
    
  }),
  State[*end for*]
)



#table(
  columns: 3,
  rows: 2,
  [  ],
  [1],
  [2],
  [#v(1mm)
    $e_1^* overline(R_1)$
    #v(1mm)
  $e_2^* overline(R_2)$
  #v(1mm)
$e_3^* overline(R_3)$

$overline(R)\

Lambda\

overline(L_1)\

overline(L_2)\

overline(L_3)$],

[#v(1mm)
  $(e_1^*) / mu_1 (1+o) = 2\
  (e_2^*) / mu_2 (1+o) = 1\
  (e_3^*) / mu_3 (1+o) = 1\
  4\
  1/4\
  1/2\
  1/4\
  1/4
  $
],
[#v(1mm)
  $2(1+1/2)=3\
  1(1+1/4)=5/4\
  1(1+1/4)=5/4\
  11/2\
  4/11\
  12/11\
  15/11\
  5/11
  $
]
)

*Extensions de MVA*
- fies avec 1 serveur, service exponentiel, FCFS
- nombre infini de serveurs, temps de service général
#h(5mm)  $overline(R_i)(M) = overline(S_i)$



Etude des files avec infinité de serveurs: 

  M/M/$infinity$

  M/D/$infinity$
  
$Pi_1 = rho dot Pi_0$

$Pi_2 = (rho/2) dot Pi_1 = (rho^2/2)* Pi_0$

$Pi_k = rho/K dot Pi_(K-1) = rho^K/K! dot Pi_0$

$Pi_0 dot (1 + rho + ... + (rho^K/K!) + ... ) = 1 $

$ Pi_0 = e^-rho$  

$Pi_K = (rho^K/K) dot e^-rho  $

M/D/$infinity$

$Pi_K(t) &= PP (K "clients dans la file à " t)
"Ce sont les clients arrivées entre "t"
 et" (t-D)\
 &= ((lambda D)^K)/(K!) e^(-lambda D)\
 &= (rho^K)/(K!) e^-rho
 $

 *Etude du processus de sortie d'une file M/M/1*
 
T = temps entre deux sorties

#diagram(
  node-stroke:0.1em,
  node-shape : rect,

  node((0,0),$| |$),
  node((1,0),$X$),
  node((1,0.4),$lambda<mu$, stroke:0em),
  node((-0.7,-0.2),$lambda$, stroke:0em),
  node((1, -0.4), $mu$, stroke:0em),
  node((2,0),$X$,stroke:0em),
  node((2.5,-0.4),$Lambda$, stroke:0em),

  edge((-1,0),(0,0), "-|>"),
  edge((0,0),(1,0)),
  edge((1,0),(2,0),"-|>"),
)
 
Si la file n'est pas vide:

$T = S$ et $T~ exp(mu)$

$f_S(x) = mu e^(- mu dot x) II_({x>=0})$

Si la file est vide:

$T = S + A$

où $A~exp(lambda) "et" S~ exp(mu)$

$f_T(x) &= integral^x_(y=0) f_A(y) f_S(x-y) d y \
&= integral^x_(y=0) lambda e^(- lambda dot mu) dot mu e^(-mu (x-y)) d y\
&= lambda dot mu dot e^(-mu x) integral^x_(y=0) e^(y(mu - lambda)) d y\
&= lambda mu e^(-mu x) [1/(mu  lambda) dot e^(y(mu - lambda))]_0^x\
&= (lambda mu e^(-mu x))/(mu - lambda) [e^(x(mu - lambda)) - 1]\
&= (lambda mu)/(mu - lambda) (e^(-lambda x) - e^(-mu x))

\
&= rho f_S(x) + (1-rho) f_(A+S)(x)\
&= lambda/cancel(mu) cancel(mu)e^(-mu x) + cancel(mu - lambda)/cancel(mu) (lambda cancel(mu))/cancel(mu - lambda) (e^(-lambda x) - e^(-mu x))\
f_T(x) &= lambda dot e^(- lambda x)
$

$T~ exp(lambda)$


#diagram(
  node-shape:rect,
  node-stroke: 0.1em,

  node((0,0), $| |$),
  node((1,0), $X$),
  node((3,0),$| |$),
  node((4,0), $X$),

  node((1,-0.4),$mu$, stroke:0em),
  node((4,-0.4),$mu$, stroke:0em),

  node((1,0.5),$1/(mu-lambda)$, stroke:0em),
  node((4,0.5),$1/(mu-lambda)$, stroke:0em),

  

  edge((-1,0),(0,0), $lambda$, "-|>"),
  edge((0,0),(1,0)),
  edge((1,0),(3,0),"-|>"),
  edge((3,0),(4,0)),
  edge((4,0),(5,0), "-|>")
)




#diagram(
  node-shape:rect,
  node-stroke: 0.1em,

  node((0,0), $| |$),
  node((1,0), $X$),
  node((3,0),$| |$),
  node((4,0), $X$),

  node((1,-0.4),$D$, stroke:0em),
  node((4,-0.4),$D$, stroke:0em),

  edge((-1,0),(0,0), $lambda$, "-|>"),
  edge((0,0),(1,0)),
  edge((1,0),(3,0),"-|>"),
  edge((3,0),(4,0)),
  edge((4,0),(5,0), "-|>"),

  edge((2.6,-0.3),(3.3,0.3)),
  edge((3.3,-0.3),(2.6,0.3)),
)

$E(L) = (rho(2-rho))/(2(1-rho))\
E(R) = (rho(L))/lambda$
#pagebreak()
*Méthode d'accès aléatoires Aloha*

#diagram(
node-shape:circle,
node-stroke:0.1em,

node((1,-1), " "),
node((1,1), " "),
node((1,0),$dots.v$,stroke:0em),

edge((-1,0),(0,0),"-|>", $lambda$),
edge((0,0),(1,-1)),
edge((0,0),(1,1)),
edge((1,1),(2,0)),
edge((1,-1),(2,0)),
edge((2,0),(3,0),"-|>"),
edge((2,0),(2,1),"-|>")
  
)

taille de trame constante, temps d'émission T.

#figure(
  image("images/20250408_115611.jpg", width: 60%),
)

Période de vulnérabilité $[-T, T]$

$PP("succès") = e^(-2lambda T)$
Occupation du support par des transmissions réussies

$Theta = lambda T e^(-2 lambda T)$, $lambda T$ la charge

$G= lambda T$

$Theta(G) = G e^(-2 G)\
Theta'(G) = e^(-2G){1-2 G}$

#table(columns: 3,
[G],[0 #h(9mm) $1/2$], [$1/2$ #h(9mm) $infinity$],
[$theta'$], [#h(7mm) +],[#h(7mm) -],
[$theta$],$#h(7mm) arrow.tr$,$#h(7mm) arrow.br$)


$Theta(1/2) = 1/2 e^(-1) = 1/(2e) = 0,18$

Vulnérabilité $[-T, 0]$

$PP("succès") = e^(-lambda T)$

$Theta = lambda T e^(-lambda T) = G e^(-G)\
 Theta'(G) = e^(-G) (1-G)$

#table(columns: 3,
[G],[0 #h(9mm) $1$], [$1$ #h(9mm) $infinity$],
[$theta'$], [#h(7mm) +],[#h(7mm) -],
[$theta$],$#h(7mm) arrow.tr$,$#h(7mm) arrow.br$)
$Theta(1) = e^(-1)=1/e = 0.36$

#diagram(
node-shape:circle,
node-stroke:0.1em,

node((1,-1), " "),
node((1,1), " "),
node((1,0),$dots.v$,stroke:0em),

node((0,2)," "),
node((0,4)," "),
node((0,3),$dots.v$,stroke:0em),

node((-0.5,-0.2),$Lambda$,stroke:0em),


edge((-3,0),(0,0),"-|>", $lambda$, label-pos:20%),
edge((0,0),(1,-1)),
edge((0,0),(1,1)),
edge((1,1),(2,0)),
edge((1,-1),(2,0)),
edge((2,0),(3,0),"-|>"),
edge((2,0),(2,3),"-|>"),
edge((2,3),(1,3)),
edge((1,3),(0,2)),
edge((1,3),(0,4)),
edge((0,2),(-1,3)),
edge((0,4),(-1,3)),
edge((-1,3),(-2,3)),
edge((-2,3),(-2,0))
  
)


On suppose que le trafic émis sur le support suit une loi de Poisson de Paramètre $(Lambda T)$



































































