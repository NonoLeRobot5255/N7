/*----------------------------------------------------------------------------*/
/*      Implantion des fonctions de base du mode utilisateur.                 */
/*                                                                            */
/*                                                  (C) Manu Chaput 2002-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>
#include <manux/appelsysteme.h>

#include <unistd.h>

appelSysteme0(NBAS_BASCULER_TACHE, int, basculerTache);

appelSysteme0(NBAS_IDENTIFIANT_TACHE, int, identifiantTache);

appelSysteme0(NBAS_DUMB, int, appelSystemeInutile);

typedef void (CorpsTache());

appelSysteme2(NBAS_CREER_TACHE, int, creerNouvelleTache, CorpsTache, booleen);

#ifdef MANUX_TUBES
appelSysteme1(NBAS_TUBE, int, tube, int *);
#endif

