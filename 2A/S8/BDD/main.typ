#import "template.typ": *
#import "@preview/fletcher:0.5.6"  as fletcher: diagram, node, edge
#import fletcher.shapes: diamond
#show: project.with(
  title :  "Base de données",
  generalites: ("SQL pas au programme de l'examen (peu en fait)"," Méthode de normalisation à l'éxam"),
  definition: ("Association","Relation (au sens mathématique) entre 2 entités", "Arité", "Nombre d'attributs d'un schéma relationnel", "SPI", "Sans perte d'information","FNBC", "Forme Normale de Boyes-Codd","FN","Forme Normal")
)

= Introduction

* Notation*
Pour l'exam
Il lit notre schéma, en fait un résumé, et c'est le résumé qui est noté.
Peut-être un peu de SQL, mais pas beaucoup, au max quelques requêtes.


*Disclaimer*
On se penchera pas sur le fond de la crypto.

== Attaques Cyber

*Risques en cas de clic sur lien:*
- Vol de données (via cookies par ex) ;
    - détruites (si extraites/existent plus sur appareil) ou chiffrées/cryptées (rançongiciel/ransomware) ;
      - On peut le contrer/parer avec des sauvegardes (qui sont "isolées" des données pour éviter que le virus les atteigne).
    - Lecture de données : Si le pirate se contente de lire les données on ne sait pas si il les a lu et on risque une usurpation d'identité sans le savoir.
      - On le contre en chiffrant les données


Crypter les données est le principe des BDDs et pour les sauvegarder c'est mieux d'avoir toutes ses données au même endroit $->$ BDDs centralisées.

- Et évite les risques liés au chiffrage/destruction.

=== Format d'un fichier POV Crypto:

2 mauvaises idées :
+ employer des listes chaînées ;
  - Si on compromet 1 truc dans la chaîne, tout ce qui arrive après est compromis ;
  - le sys d'exploitation (donc le hackeur) connais l'ordre d'entrée des données.
+ employer des tableaux.
  - l'ordre du tableau donne un indice à un éventuel pirate.

$=>$ solution techinque est la *table de hachage (ou hashtable)*

La BDD est une réservation d'espace, la donnée est à une $@$ h (clef) avec h fonction de hachage compliquée à reverse sans la clé.


* Modèle principal : modèle relationnel*

Plan du cours :
- Modèle Entité-Association (pratique pour la conception d'un schéma BDD) ;
  - Employé dans *MERISE*
- Modèle relationnel ;
  - Définition ;
  - Normalisation relationnelle.



= Modèle Entité-Association



Etonnant, on y trouve... des entités, ET des relations (non, jure)
(dinguerie #emoji.face.shock) 

*2 concepts :*
+ Entité ;
  - quelque chose qui existe dans le monde réel ;
  - Ce n'est pas imprimable ;
  - Ce n'est connu que par ses attributs ;
    - les attributs sont imprimables ;
    - Il y a forcément un identifiant parmi ces attributs, l'identifiant est souligné pour l'identifier ;
    - Il est atomique (on mets pas plusieurs entrées dans un même attribut ex: pls prénoms dans le même champ prénom).

  *exemple*
  #table(
  columns: 1,
  [Personne (entité)],
  [- nom ;
- prénom ;
- $@$ ;
- date de naissance.
- $dots$]
)


+ Association 
   - relation entre 2 entités (au sens mathématique) ;


  #diagram(
       node((0,0.5), table(
      columns: 1,
      [Employé (entité)],
      [- #underline[#text("# employé")];
      - $dots$]
    )),
        node((2,0.5),table(
      columns: 1,
      [Département (entité)],
      [- #underline[nom];
      - $dots$]
    )
  ),
  node((1,0), "Travail", stroke : 0.1em, shape: diamond),
  node((1,1), "Chef", shape : diamond, stroke : 0.1em),
  node((-1,1),"Participe", stroke : 0.1em, shape: diamond),
  node((0,2),"Projet",stroke :0.1em),

  edge((0,0.5),(1,0), $1.1$, label-pos : 30%),
  edge((0,0.5),(1,1), $0.1$),
  edge((1,0),(2,0.5), $1.n$,label-pos : 70%),
  edge((1,1),(2,0.5), $1.1$),

  edge((0,0.5),(-1,1),$0.m$),
  edge((-1,1), $1.N$),
  edge((-1,1), (-1,1.5), $%"Ps"$,label-pos : 100%)
  )

*Raisonnement multiplicité:*
+ Employé - Département
  - Un employé travaille dans un et un seul département;
  - Un département comporte N employés ;
  - Un département comporte au moins 1 employé.
  - Donc multiplicité: $1 dots N$ ou  "1 dots $infinity$ ou $1 dots *$ du coté département.
#citation([On est pas à l'armée mexicaine, tout le monde n'est pas chef],[Pascal Ostermann],[14 mars 2025])

  
+ Employé - Projet
  - Un employé peut être sur 0 ou plusieurs projets
  - donc multiplicité $0 dots N$ do coté 
  - Un projet a au moins un employé et peut en avoir plusieurs
  - donc multiplicité $1 dots N$ du coté 

#citation([ça va être de la sodomie ],[Pascal Ostermann],[14 mars 2025])


  
Il existe des associations ternaires, quaternaires, et en général N-aires.

Une relation R est arité SSI elle est N-aire.

#diagram(
       node((0,0.5), table(
      columns: 1,
      [Personne (entité)],
      [- #underline[#text("# assuré")];
      - $dots$]
    )),
        node((2,0.5),table(
      columns: 1,
      [Objet (entité)],
      [- #underline[#text("#")objet];
      - $dots$]
    )
  ),
   node((1,1),table(
      columns: 1,
      [Compagnie d'assurance (entité)],
      [- #underline[nom];
      - $dots$]
    )
  ),
  node((1,0), "Assure", stroke : 0.1em, shape: diamond),
  

  edge((0,0.5),(1,0), $1.n$),
  edge((1,0),(2,0.5), $1.n$),
  edge((1,0),(1,1),$0.n$,label-side: right),
  edge((1.1,0),(1.1,0.4),label:"risque")

  )



== Exemple Partie d’échecs:


 #diagram(
     node((0,0), table(
        columns: 1,
        [Joueur (entité)],
        [- #underline[n° licence] ;
      - prénom ;
      - $dots$])
   ),
   node((3,0), "Partie", stroke : 0.1em, shape : diamond),

   edge((0,0), (3,0), bend : 30deg, label : "Blanc" ),
   edge((0,0), (3,0), bend : -30deg, label : "Noir"),
   edge((3,0),(3,0.7), label : grid( columns: 1,[table], [round], [résultat]), label-side : left, label-pos: 40%)
)


*Multiplicité*
+ Joueur/Partie
  - On peut avoir, au 1er round joué qu'une seule couleur (donc pas l'autre)
  - Au bout de plusieurs rounds, on peut avoir joué soit l'autre couleur, soit re la notre
  - donc multiplicité de chaque couleur: $0 dots N$.


=== Autre possibilité de la partie d'echec

#diagram(
     node((0,0), table(
        columns: 1,
        [Joueur],
        [- #underline[n° licence] ;
      - prénom ;
      - $dots$])
   ),
   node((5,0), table(
        columns: 1,
        [Partie],
        [- table ;
      - ronde ;
      - résultat.])
   ),
   node((2.5,-0.5), "Blancs", stroke : 0.1em, shape : diamond),
   node((2.5,0.5), "Noirs", stroke : 0.1em, shape : diamond),

   edge((0,0), (2.5,-0.5), label : $0.n$ ),
   edge((0,0), (2.5,0.5), label : $0.n$ ),
   edge((2.5,0.5), (5,0), label : $1.1$ ),
   edge((2.5,-0.5), (5,0), label : $1.1$ ),
   
)


#citation([Celui qui joue avec les noirs],[Pascal Ostermann],[14 mars 2025])



== Modèle de PP Chain (= ou == ?)
$=>$ Se voulait à l'origine un modème d'interface entre le modèle relationnel et le model réseau CODASYL.

Sert maintenant pour parler avec un client et comme modèle de conception.
- A donné naissance à MERISE et MERSISE2/EURO MERISE.


Certains modèles Entité-Association rajoutent des constructeurs (souvent orienté objets).


*Le prof proscrit tout ceci:*
+ Attributs:
  - Structurés ; 
  - Multivalués ; 
  - Facultatifs (valeur NULL) .
+ IS_A (relation d'Héritage) ;
  - disjonction.
+ Entités faibles (qui n'ont pas d'identité) ;
+ Associations faibles (qui ne serait pas identifié par les entités qu'elle lie) 


C'est surtout un modèle graphique qui peut se faire petit bout par petit bout.
- facilement compréhensible ;
- très facile à transformer en du relationnel.

*Exemple :*

- Personne (#underline[num assuré], nom, date) ;
- Objet_assuré (#underline[num objet], description) ;
- Compagine_assurance (#underline[nom, $@$], tél) ;
- Assure (#underline[num assuré], #underline[num objet], #underline[nom, $@$], risque )







*Et on oublie pas la QoS *



#citation([Mon dieu que j'écris mal],[Pascal Ostermann],[14 mars 2025])
Je confirme _Pierre_ |
de même _Léa_
| tout pareil _Nolann_

== Modèle relationnel

=== Premier modèle étudié
#grid(columns: 2, column-gutter: 10mm, [
  $\
  \
  \
  R(A_1 dot D_1, A_2 dot D_2,dots , A_n dot D_n) $
],
[- $R$ : nom de relation

- $A_2$ : nom d'attribut

- relation n-aire, d'arité n]
)

#linebreak()
*On doit toujours avoir le domaine en tête, ici on les précise pas car évident*


*Exemple : *$"Etudiant"("Numéro"_"etu","nom"_"etu", "prénom"_"etu", "titre"_"cours", "heure"_"cours", "salle"_"cours")$
*Ici, ça ne va pas car des infos peuvent être redondantes* car le fait qu'un cours ai lieu dans une salle sera dupliqué $n_"eleve"$-fois (une fois par élève)

_ex de $n_"uplet"$_ : $(666, "Felixe", "Ceras", "Info", 14h, "A002")$


les infos: (Info, 14h, A002) sont répété autant de fois qu'il y a d'étudiant en info, il y a une *redondance* $=>$ si on modifie la salle d'un cours il faut modifier $forall$ étudiant inscrit au cours
- au mieux c'est coûteux ;
- au pire risque d'incohérence.

*Conclusion*: Multiplier une info c'est risquer qu'une des infos soit modifiée sans modifier les autres itérations.

En base de données, on considère que l'utilisateur ne connaît rien.


=== Autre schéma possible de BDD

$"Et"("numéro"_"etudiant", "nom", "prénom")$
$"cours"("titre", "heure", "salle")$
*perte d'info : il manque  Suit($"numéro"_"étudiant",$ titre)*

#v(3em)

*Normalisation relationnelle : montrer que ce résultat est le bon* #linebreak()

Digression1 : #underline[algèbre relationnelle] $->$ dérivée de la théorie des ensembles ( t est dans une relation R $<=>$ t $in$ R)

#h(5mm) #box([Opérateurs unaires. Projection et sélection

Projection $Pi$ en $Pi_("#etu, nom_etu, pr_etu")$ Etudiant $->$ Et

Sélection $sigma$ axiome de sélection de Ajermelo-Fränhel

Si $EE$ est un ens et $phi$ une condition alors ${x in EE  | phi(n) }$ est un ensemble.

condition de sélection : $A Theta B$ ou $A Theta "cte"$ 
avec (A,B attributs; $theta in {=,!=,<,<=,>,>=}$ )

- Si C et C' sont des conditions de sélection 
$=>$ $not C, C or C', C and C', C' in C, dots$ sont des conditions de sélections

liste des cours après le 1er avril à 14h :
$sigma_("date">#text["1er avril 14"])$Cours
])
*Opérateurs ensemblistes* : $union, inter, - $ (réunion, intersection, différence)


Deux relations sont $union$-compatible ssi :
- elles sont de même arité ;
- les attributs correspondants sont de même domaine

On peut faire la réunion/intersection/différence que sur des relations U-compatibles.

#citation([*Nolann* : Désolé mais je peux pas lire ce mot 

*Pascal Ostermann* : Moi non plus
], [Nolann Martin & Pascal Ostermann], [21 mars 2025])



*ex :* Cours suivi par aucun étudiant

$ Pi_("titre")"Cours" - Pi_("titre")"Suivit" $

Produit cartésien, jointure :

$R times S = {(x_1,,dots,x_n, y_1, dots , y_n) | (x_1, dots, x_n) in R, (y_1, dots, y_n) in S }$

R est n-aire, S m-aire

$ R join_C S = sigma_C (R times S) $
C la condition de jointure

- equi-jointure = une jointure où la condition de jointure est une conjonction d'égalité

- jointure-"naturelle" = une equi-jointure sur les attributs de même nom.

_ex: etu $join$ Suit $join$ Cours = Etudiant_ $->$ Décomposition SPI

On dit qu'une décomposition $R -> S_1,dots,S_n$ est *sans perte d'information (SPI)* ssi $R join S_1 join dots join S_n\
R -> S_1, dots ,S_n$


*L'algèbre peut se définir à l'aide de $union, -, sigma, Pi "et" times$*

($R inter S = R - (R-S)$)

L'opérateur coûteux de l'algèbre est la jointure ($join$).

$R join S$ de l'ordre de $"taille"(R) * "taille"(S)$

avec un "index", sur les domaines concernées de S $"taille"(R)times "log"("taille"(S))$

Mais cela reste très coûteux. 


$=>$ Au final cela optimise les mise à jour et les requêtes.

#citation([Pour que mon q (cul) soit une abréviation de requête et pas autre chose
],[21 Mars 2025],[Pascal Ostermann])

Digression 2 : #underline[Dépendances Fonctionnelles (DF)]

X et Y un ensemble d'attributs d'une relation R
$X -> Y$ est vraie dans la relation R ssi "X détermine Y":
$ forall s, t in R #h(3em) s dot X = t dot X => s dot Y = t dot Y $
$s dot X <=> #text(["projection de s sur X"])$  

*Ex:*

Si $Y subset X #h(2mm) X -> Y "DF" $

Si X $->$ Y et Y $->$ Z alors X $->$  Z

X $->$ Y et Z $->$ Z $  $<==>$ X $->$ "YZ"

"#-etu" -> "nom"_"etu","prenom"_"etu"$

$"salle"_"cours","heure"_"cours" -> "titre"_"cours"$

une DF est réduite à gauche $X -> Y$ ssi [$Z subset Y$ et $Z -> Y => Z = X$]

K est une *superclef* de R ssi $K-> R$(abus de langage pour l'ensemble des attributs de R)

Une clef = une superclef minimale  pour l'inclusion.

#theo([
  
Tout relation a une superclef
])


#theo[
  
Toute relation a au moins une clef
]
*
A partir de maintenant, je veux qu'on souligne une clef $=>$ c'est la clef primaire la clef d'accès à la table de hachage*

#citation([à savoir que j'écris clef avec un "f" et pas avec un accent sinon on ne peut pas lire],[Pas cal Ostermann (aka l'Homme de l'Est)],[21 mars 2025])


#theo[Théorème de décomposition

$X -> Y$ ($X, Y$ disjoints) et DF vraie dans $R$ 

alors R se décompose SPI en $Pi_X (R) "et" Pi_(C_y) (R)$


]

#met[*décomposition*

utiliser le théorème de décomposition jusqu'à obtenir des formes normales]

Forme Normal de Boyce-Codd (FNBC) 

R est au FNBC ssi toute DF $X -> Y$

#h(5mm) #box([ V dans R est telle que 
$cases(
Y subset X ("DF triviale"),
"ou" ,
X "est superclef "
)$])



#theo[

Toute relation peut se décomposer SPI en des relations en FNBC
]

#citation([J'aurais jamais pensé apprendre les bdd avec un ancien hippie ],[SORRES Antonin], [28 mars 2025])


_Exemple de normalisation:_      programmation multiplexe cinéma

Liste des attributs:
- nom_salle
- capacité_salle
- titre_film
- date_séance (format inclus l'heure)

Relation "globale" : R(#underline[nom_salle], capacité_salle, titre_film,#underline[date_séance])

DFs:
- nom_salle $->$ capacité_salle (1)
- nom_salle & date $->$ titre_film (2)
- titre_film $->$ nom_salle (On dit qu'un film ne passe que dans une salle) (3)

R n'est pas un FNBC à cause de  (1)
+ On applique le théorème de décomposition $->$ R se décompose SPI :
  - Salle(#underline[salle],capacité)
   - Et un reste
  N'est toujours pas FNBC $->$ (3)+ théorème de décomposition 
  
  
  Programmation(#underline[titre_film],nom_salle)
  - Et un reste (titre_film, date_seance)

Pour avoir l'information complète: "film X passe à heure Y dans salle Z" $->$ il faut faire une jointure (coûteux).

On se demande donc si c'est pas mieux de réster sur l'étape d'avant :
- Salle
- Programmation2(#underline[nom_salle], titre_film, #underline[date_séance]) $=>$ pas en FNBC mais en 3e FN et c'est une décomposition sans perte de dépendance

*Troisième Forme Normale (3FN)*

R est en 3e FN $<=>$ toute DF $X -> A$ (A attribut) ... des R est tel que

- X superclef

- A $in$ X
 
- A fait partie d'une clef

Donc:
FNBC $=>$ 3e FN
Toute relation peut se décomposer en SPI et sans perte de dépendance en des relations en 3e FN

#def([*Formes normales*

+ 1ère Forme Normale (obsolète): à l'origine, dans une "case" de tableau, il pouvait y avoir des valeurs non-atomiques. La 1ère FN disait que ces valeurs étaient atomiques.
  
  Relationnel Non Formal?? Normal Form (NFNF ou NF2)
  - dans une "case" du tableau il peut y avoir une relation 
  - variante de l'E...???
+ 2e Forme Normale : 
  
  Si une DF $K -> Y, K "est une clé"$ viole des codes de la $3^("ème")$ FN
  
  - Deuxième cas $Z<=K$,  $Z->T$, $T<Y$:il y a une DF potentielle ou non élémentaire.
    
  - Ou alors; $K -> Y$ et $Y -> Z$ $=>$ Il y a une DF teaudtine??? ou non directe.


  Lorsque nous établissons une liste des DFs, il faut l'éllaborer de la manière la plus concise.

  En particulier pas de DF partielle 

  suite transitive : 
    - si on ecrit $X->Y$ et $Y->Z$
    - sinon si on ecrit $X -> Z$
+ 4e Forme Normale: R est en 4e Forme Normale (4NF) ssi toute DMV $X -> Y|Z (X,Y,Z "partitions de R")$
  - et .... Y = 0 ou Z = 0 (DMV triviale)
  - ou X super clef ( X $->$ YZ)
  - On peut toujours décomposer SPI en des relation de 4FN

])


#citation([Quand on va dans des université américaines, tant qu'il en reste],[Pascal Ostermann],[28 mars 2025])


_Exemple:_ Etudiant(num_etu, titre_cours, sport)

Pas de DF, donc en FNBC:

#table(
  columns: 3,
  [#text("#et")],[cours],[sport],
  [813],[Histoire],[Savate],
  [813],[Géo],[Escrime],
  [813],[Géo],[Savate],
  [813],[Histoire],[Escrime],
)

on tire des deux premières les deux autres car il faut toutes les associations possibles (je crois)

Il faudrait décomposer en: X(num_etu, cours), et Y(num_etu, sport)

*Dépendances Multi-Valuées (DMVs)*

soient $X,Y,Z$ disjoints $2$ à $2$

$X-> Y|Z$ vraie dans R  $ <=> forall s,t in RR   #h(5mm) & s dot X = t dot X => \

&exists u #h(2mm) X = s dot X 
&"si" Y = s dot Y\
&"si" Z = t dot Z $


#theo([*Décomposition pour les DMVs*

Si $X,Y,Z$ partition de R 

$X -> Y|Z <=> $ R se décompose en SPI en $Pi_(X Y) (R) "et" Pi_(X Z) (R) $

])

$X -> Y | Z <=> Z | Y$

$X -> Y | emptyset  $ est vraie 

$X, Y $disjoints alors $X ->Y -> X -> Y | Z$ #h(5mm)$forall Z$ disjoint de X et de R

4 FN = FNBC


_Exemple:_ buveurs de bièèèèère

#citation([
Buveurs(buveur, bière, bar) une relation globale, "globalement nulle à chier"
], [hippie], [28 mars 2025])

Comment faire une meilleure relation buveurs -> bière | bar ? 

- la relation est multivaluée ssi Buveurs = Boits(#underline[buveurs, bière]) $join$ Fréquente(#underline[Buveur, bar]) 
  - Ici perte de l'info Sert

- bière $->$ buveurs | bar  ssi Buveurs = Boit(#underline[buveurs, bière]) $join$ Sert(#underline[bar, bière])
  - Ici perte de l'info Fréquence

La seule décomposition possible est:
- Buveur = Boit $join$ Frequente $join$ Sert
On dit qu'il y a une Dépendance de Jointure (DJ) et qu'il y a 5e Forme Normale ssi les DJ se déduisent des clefs

Autre normalisation pour la relation *Buveur*.
On prends comme attributs:
- Buveur2(#underline[Buveur, bbière_bue, bar, bière_servie])
  - buveur $->$ bière_bue | bar, bière_servie
  - bar $->$ buveur | bière_servie

  $=>$ Fréquente, sert, boit.




=== Méthode de normalisation
*A réviser sinon hippie pas content*

+ Etablir une liste des attributs (indépendants les uns des autres)
  - *Pas d'attributs calculables.* (ex: nombre de cours) => à proscrire
  - Que des attributs #underline[atomiques] (pas de listes)
  - Éviter les boucles de signification

+ Lister les Dépendances Fonctionnelles et Multi-Valuées (DF, DMVs)
  - Pas de dépendances fonctionnelles transitives
  - pas de dépendances partielles
  - toutes les DFs réduites à gauche

+ Décomposition la plus puissante possible


== Résumé Normalisation

- #underline[DFs + theo de décomposition pour les DFs]
  - 1FN : totalement optionnel (on s'en fous)
  - 2FN : optionnel
  - #underline[3FN] "dénormalisation"
  - #underline[FBNC] (_la plus importante_) + thm de décomposition pour DMV
  - #underline[4NF]: 
  - #underline[5FN] : à éviter




= Languages relationnels

- Language de Définition des Données (LDD)
  - défini des relations, des cléfs, primaires et secondaires, des indexes, des attributs
- Language de Manipulation des Données (LMD)
  - mises à jour (MAJ)
  - requêtes (q̂)
    - écriture de Algèbre relationnel
    - fonctions d'agrégation résultat "statistique"

= SQL (Structured Query Language)

C'est un language déclaratif avec optimisation implicite

== Algèbre relationnelle en SQL
c'est la complétude au sense de Codd

_Exemple du TD1:_

- Symbole(#underline[GPS], valeur)
- Lieu(#underline[GPS], nom, tel, GPS_Sym)
- Ligne(#underline[GPS], nature, nom, desc)
- Rencontre(#underline[GPS_ligne], GPS_sym, #underline[num d'ordre])


lire de la manière:

_forme en algèbre relationelle $<==>$ requete sql_

- Pour récupérer des infos:
$Pi_("nom", "tel")$ Lieu $<==>$ SELECT nom, tel FROM Lieu;

- Pour selectionner certaines infos particulières
$sigma_("nature = 'cours d'eau") "Ligne"$  $<==>$ SELECT \* FROM Ligne WHERE  nature = \'cours d eau\'


- $inter, union, -$ : UNION, INTERSECTS, MINUS

Symbole qui ne corresponds à aucun Lieu.
En algèbre relationelle : $Pi_("GPS")$ Symbole $-$ $Pi_("GPS")$ Lieu 

En SQL: 

$& "SELECT GPS FROM Symbole"\
      &"MINUS"\
      &"SELECT GPS_symbole FROM Lieu;"$



- Produit cartésien de 2 relations R et S:

SELECT $"<Des attributs>"$ FROM R,S;

#text(fill: red)[*Attention* sans \"WHERE\" cela donne le produit carthésien]

- Liste Des "Hébergements":

$Pi_("Lieu, GPS, tél") (sigma_("nature = hébergement")) join "Lieu"$

SELECT Lieu, GPS, tél FROM Symbole, Lieu WHERE nature = \'hébergement\' AND Symbole.GPS = Lieu.GPS_Symbole


#v(20mm)
SQL est complet au sens de Codd (ie: permets d'exprimer l'algebre relationnel)

- Autre écriture de la jointure($join$) précédente:

#h(5mm) SELECT GPS, tél FROM Lieu

#h(5mm) WHERE GPS IN

#h(5mm) (SELECT GPS_Symbole WHERE nature = \'hébergement\');

#text(fill: red)[*Attention* parenthèses obligatoires: sinon on sait pas de quel "WHERE" on parle.]

 
- *IN* est un prédicat du $2^("nd")$ ordre, #h(5mm )usage : A IN (SELECT ...) est vrai ssi A est un élément de (SELECT ...)

- "Grande" jointure utile si en résultat, on veut des attributs vennant des 2 relations.

SELECT utile surtout pour des MAJs.

_par exemple:_ 

UPDATE Lieu WHERE GPS_Symbole IN 

(SELECT GPS FROM Symbole WHERE nature = \'hébergement\')

SET desc = \'hébergement\' $and$ desc;

$and$ : Concaténation de chaînes de caractères


- Tout les prédicats du $2^("nd")$ ordre: NOT IN, CONTAINS $dots$
    - Cas du *NOT IN*: tout les Symboles qui ne correspondent à aucun Lieu


SELECT GPS, nature FROM Symbole

WHERE GPS, NOT IN (SELECT GPS_Symbole FROM Lieu)

(S1) CONTAINS (S2) ssi S2 $subset$ S1 (inclusion ensembliste)

#text(fill: red)[*\/!\\* S1 et S2 sont totalement indépendants de l'extérieur. Il faut écrire EXPLICITEMENT les conditions de jointure]


#pagebreak()
== Fonctions d'agrégation

Calculer des sommes (*COUNT, AVG, $dots$*)

- Nombre de symboles sur la carte:

SELECT COUNT($"*"$) FROM Lieu;

#h(5mm) COUNT($"*"$) => compte les lignes

#h(5mm) COUNT(nom) => compte les lignes où nom est NOT NULL

#h(5mm) COUNT(tel) => compte les lignes où tel n'est pas vide

#h(5mm) COUNT(DISTINCT tel) => compte les lignes où les tel sont distincts (et non NULL)

=== Digression sur les valeurs nulles

Valeur nulle NULL $->$ valeur nulle de Codd (non-existentielle : la valeur n'est pas définie) 

$-->$  $cases(
"NULL" = 4 -> "NULL",
"NULL" - 7 -> "NULL",
"NULL" = "NULL" -> "NULL",
"NOT NULL" -> "NULL"
)$

SELECT \* FROM Lieux WHERE tel IS NULL;

$->$ reponse vide

pour obtenir les lieu dont le tel n'est pas NULL : operateur IS NOT

Dans une proposition (en logique), est interprété comme Faux


*Tous les cours d'eau avec leur nb de points, mais seulement pour ceux qui ont + 10 points :*

SELECT Ligne, GPS, nom, COUNT(DISTINCT num_ordre)

FROM Ligne, Rencontre

WHERE nature = \'cours d eau\'

AND Ligne.GPS = Rencontre GPS.ligne

GROUP BY Ligne.GPS, nom

HAVING COUNT(DISTINCT num_ordre) > 10;

Autres fonctions d'agrégation SUM, AVG, MIN, MAX, VARIANCE, $dots$

*Listes des points du GR32, dans l'ordre :*

SELECT Rencontre.GPS.Point FROM Ligne, Rencontre WHERE Ligne.GPS = Rencontre.GPS.ligne ORDER BY num_ordre;


Note: jsp ce qu'il cook mais il a repris la Query d'avant avec des modifs pour en faire une vue:

#text(fill: rgb("593532"))[CREATE VIEW Statistiques AS]

SELECT Ligne, GPS, nom, COUNT(DISTINCT num_ordre) #text(fill: rgb("593532"))[nombre de points]

FROM Ligne, Rencontre

WHERE nature = \'cours d eau\'

AND Ligne.GPS = Rencontre GPS.ligne

GROUP BY Ligne.GPS, nom

HAVING COUNT(DISTINCT num_ordre) > 10;

#text(fill: rgb("593532"))[en brun, operateur de renommage]

Attention, il est hors de question d'utiliser un ORDER BY sur une vue

vue: représentation d'un calcul sous forme de relation, la vue statistique est recalculée chaque fois qu'on l'utilise.



#def[*MERISE*

Méthode d'Etude et de Représentation Informatique des Systèmes d'Entreprise]

système d'information -> la mémoire de l'entreprise = données + traitements (tts)

Principe de MERISE : étude séparée des donnes des tts

#table(
  columns:2,
  [Données (E-A)], 
  [Traitements],
  [Modèle conceptuel des données brut
  
$arrow.b$

validation $arrow$ Modèle validé

$arrow.t$

Modèles externes],
  [Modèle conceptuel des traitements

#v(5mm)
#h(10mm) $arrow.b$

#v(5mm)



$arrow.l$Phases #h(5mm) $cases("manuelle","automatique","converssationnelle (homme/machine)" )$]
)




Rapport (pas sûr) : Phases / MXs

  On peut dire quelles données sont utiles à tel traitement.

  $(*1)$

  #table(
    columns: 5,
    [traitements données ],[R1],[R2],[$dots$],[Rn],
    [traitement 1], [X], [s], [$dots$],[s/w],
    [traitement 2], [w],[x],[$dots$],[x],
    [$dots$],[],[],[],[],
    [traitement m],[]
  )

  $=>$ je peux savoir combien de fois sont appliquées $cases("telle jointure", "ou","telle màj")$

  $->$ fichiers : représenté par une table de hachage 

*  problème :* 
- optimiser les màj $=>$ rend difficile la moindre requête.

- optimiser les requêtes $=>$ dégrader les màj.

- optimiser les requêtes c'est rajouter une donnée là où il y en a déjà une, il y a collision -> deux données identiques pour la fonction de hachage.
  En cas de collision: 
  - hachage linéaire : on met alors le donnée à la case suivante .
  - hachage quadratique
  -on applique une seconde fonction de hachage

Complexité d'un ajout de données = nombre moyen de collisions $arrow$ nettoyer les données inutiles rend plus efficace les recherches.

Compléxité d'une jointure  entre deux relations R et S

o(tailleR $*$ taille S) sans index (outil d'optimisation)

o(taille R $*$ nombreDecollisionsDeS) avec index 

problème de l'index : 

  - quand on ajoute une donnée il faut aussi mettre à jour l'index.

Les choix d'optimisation :

  - mettre un index ou pas
  - forme normale plus ou moins forte peuvent se déduire du tableau ($*1$)

Les modèles externes se déduisent assez facilement.


à l'examen :
- pour SQL il est possible qu'il y ai 2 ou 3 questions dessus très simple.
- $@$ mail du prof sur le TD2 pour les questions                                            









  