= Réseau de Petri : modélisation et propriétés

== Exercice 1

+ les différents éléments sont : 
    - jetons 
    - places (ronds)
    - transitions (carrés)
    - arcs (flèches)
+ Évolution du réseau de Petri :
  - On considère les sommets nommé A,B,C,D,E
  - $(B->A)$ et $(D->E)$
  - $(A->B,C)$ et $E$ stagne
  - $(B->A)$ et $(C,E->D)$
  - $(A->B,C)$ et $D->E$
  - etc...
  Sauf que problème parce qu'on créer plus de jetons qu'on utilise au final on va saturer le Tampon (C)
+ Pour éviter cela on peut ajouter un état intérmédiaire (F) et les arcs 
   - $(F->("transition entre A et B"))$ 
   - $(("transition entre C et D") -> F)$
+ on a :
  $M_0 = mat(P_1=0;
            P_2 = 1;
            P_9 = 0;
            P_4 = 1;
            P_3 = 0;
            P_(10) = 3;
            )$