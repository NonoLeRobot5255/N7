# Objectif général

   Mettre en place les outils de synchronisation permettant d'assurer le bon fonctionnement
des tubes de communication (équivalent du pipe Unix) dans "ManuX".

   L'implantation des tubes est fournies.

   On implantera, une version bloquante et une version non bloquante
(au sens des E/S Unix : lorsque aucune donnée (ou place) n'est
disponible, l'appel système de lecture (ou d'écriture) peut-être
bloqué ou peut renvoyer la valeur nulle (pour la version non
bloquante).

# Compilation de ManuX

   On compile et on lance le noyau (dans un émulatur qemu) de la façon
   suivante. 

   ```
   make
   make run
   ```

   Chaque tâche (ainsi qe le noyau) dispose d'une console. On peut
basculer entre les console avec la touche ESC. Dans la console noyau, 
quelques touches permettent d'observer certaines informations
basiques, par exemple la touche "s" permet de voir l'état des outils
de synchronisation (exclusions mutuelles et conditions).

## Le code

   Le code source est réparti dans quelques répertoires.

   L'implantation des tubes est dans le répertoire `sf`.

   L'implantation des "programmes utilisateurs" est dans `usr`,
c'est ici le fichier `usr/init-acces-concurrent.c` (fourni) qui sera utilisé.

# Les tubes

## Implantation

   Le fichier `sf/tubes.c` (et `include/manux/tubes.h`) implante (et définit)
l'objet tube.

   Les fonctions les plus importantes ici sont les suivantes

   
```
   tubeOuvir()
   tubeFermer()
   tubeLire()
   tubeEcrire()
```
   Chacune d'entre elles est invoquée lorsqu'une tâche utilise l'appel
système du même nom.

   De plus, la fonction `sys_tube()`  est invoquée à la création d'un
tube (suite à l'utilisation de l'appel système `tube()` par une tâche).

## Utilisation

   Côté utilisateur (`usr/`) :

   * Un tube est créé avec

```
int fd[2];
int r;
r = tube(fd); // ESUCCES ou ENOMEM
```

   Il est directement ouvert et ce qui est écrit (sur `fd[1]`)
peut ensuite être lu (sur `fd[0]`) dans l'ordre.

   * Un tube est manipulé avec `lire()` et `ecrire()` qui fonctionnent
comme les appels systèmes `read()` et `write()` sous Unix.

retour : le nombre d'octets lus ou écrits (si >=0) ou `-EINVAL` en
cas d'erreur

# Userland

   Le fichier `usr/init-acces-concurrent.c` implante des tâches dont
certaines écrivent et d'autres lisent dans le tube. Une partie du code
est donnée : le tube est créé (et automatiquement ouvert) et les
tâches sont créées qui lisent et écrivent dans le tube).

# Configuration du noyau

   Dans le fichier `include/config/base.h` on peut définir la macro `MANUX_REENTRANT`
sans laquelle un gros verrou empêche l'accès au noyau par deux tâches "simultanément".

##  Noyau non ré-entrant

   Si la macro `MANUX_REENTRANT` n'est pas définie, il n'y a donc qu'une tâche max
dans le noyau à un instant t, il n'y a donc pas trop de soucis avec le code du tube
qui va fonctionner (mais qui est non bloquant).

   Cela peut aider dans la compréhension des problèmes de
   synchronisation, voire dans le debogage de la solution.
   
## Noyau ré-entrant

  Dans ce cas, il est important de protéger les fonctions par des outils de synchro
afin d'assurer la cohérence des données. C'est l'objectif de ce
travail !

# Les outils de synchro

   Ils sont définis dans `include/manux/atomique.h` et implantés dans `noyau/atomique.c` et
nous utiliserons les types suivants

```
   ExclusionMutuelle
   Condition
```

   Leur utilisation et leur fonctionnement sont similaires à ceux des
   outils évoqués en cours.
   
   L'utilisation de `exclusionMutuelleEntrer()` bloque
(éventuellement) la tâche en cours jusqu'à ce qu'elle ait accès à la
zone en exclusion mutuelle. Elle est alors garantie d'y être seule,
même si elle est interompue et qu'une autre tâche
s'exécute. Lorsqu'elle utilisera la fonction
`exclusionMutuelleSortir()`, elle libèrera la place pour une autre
tâche (si une tâche était bloquée, elle sera alors débloquée).

   Lorsqu'une tache utilise la fonction `conditionAttendre(c, em)`,
l'exclusion mutuelle `em` est automatiquement déverouillée (elle
doit donc avoir été verouillée précédemment par la tâche) et
lorsque la tâche est débloquée (parce qu'une autre tâche a utilisé la
fonction `conditionSignaler()`), alors l'exclusion mutuelle `em` est
automatiquement re-verrouiller (elle devra donc être déverouiller plus
tard par la tâche).

## Le basculement entre tâche

   Le noyau ManuX est un noyau multitâche préemptif, ce qui signifie
qu'il va lui même interrompre la tâche en cours au bout d'un temps
fixé afin de donner la main à une autre tâche.

   C'est dailleurs bien là la source principale des problèmes de
synchronisation évoqués ici !

   Il est donc inutile d'utiliser explicitement des fonctions de
basculement. Pourtant, il peut être intéressant de 'forcer' des
basculements entre tâches à certains points particulier du code afin
de vérifier que les outils de synchronisation font bien leu travail.

   Pour cela :

   * En mode utilisateur (donc dans les fichiers du répertoire `usr`),
   l'appel système `basculerTache()` peut être utilisé.
   * Dans le noyau, c'est la fonction `ordonnanceur()` qui remplit ce
     rôle. 
