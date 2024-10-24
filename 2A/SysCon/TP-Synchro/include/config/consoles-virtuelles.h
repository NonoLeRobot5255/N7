#include <config/console.h>

/*
 * Utilisation (ou non) des consoles virtuelles. Si on ne les utilise
 * pas, tout ce qui est affiché est mélangé à l'écran.
 */
#define MANUX_CONSOLES_VIRTUELLES 

/*
 * Lorsqu'on crée une nouvelle console, est-ce que l'on bascule
 * automatiquement vers elle ? 
 */
#define MANUX_BASCULER_NOUVELLE_CONSOLE

/*
 * Affectation d'une console à chaque tâche. Si ce n'est pas le cas
 * (et si le reste de la configurtion le permet), ce sont les fichiers
 * associés à la tâche qui sont utilisés pour les entrées-sorties.
 */
#define MANUX_TACHE_CONSOLE
