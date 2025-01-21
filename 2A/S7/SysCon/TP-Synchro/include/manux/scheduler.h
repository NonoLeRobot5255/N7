/*----------------------------------------------------------------------------*/
/*      Définition du scheduler de Manux. Version trés minimale à revoir.     */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef SCHEDULER_DEF
#define SCHEDULER_DEF

#include <manux/types.h>
#include <manux/tache.h>
#include <manux/listetaches.h>
#include <manux/atomique.h>
#include <manux/appelsysteme.h>

/*
 * Pour permettre la gestion des consoles virtuelles. WARNING n'a rien
 * à faire là
 */
extern booleen basculeConsoleDemandee;
extern booleen afficheEtatSystemeDemande;
extern booleen basculerTacheDemande;

/**
 * @brief : L'identification de la tâche en cours
 */
extern Tache * tacheEnCours;

/**
 * @brief : La liste des tâches prêtes sur le système
 *
 * Ce sont les tâches prêtes à être exécutées. N'y figurent donc pas
 * la tâche en cours d'exécution ni les tâches en attente sur un outil
 * de synchronisation.
 */
extern ListeTache listeTachesPretes;

/**
 * @brief : La liste de toutes les tâches existant sur le système.
 */
extern ListeTache listeToutesLesTaches;

/**
 * @brief : La liste des tâches achevées
 */
extern ListeTache listeTachesTerminees;

/**
 * @brief Identifiant de la tâche actuellement en cours d'exécution
 * dans le noyau (0 si aucune)
 *
 * C'est une façon d'assurer le fonctionnement d'un noyau non
 * réentrant.
 */
#if defined(MANUX_TACHES) && !defined(MANUX_REENTRANT)
extern struct _ExclusionMutuelle verrouGeneralDuNoyau;
extern TacheID tacheDansLeNoyau;
#endif

void initialiserScheduler();
/*
 * Déclencher le scheduler avant toute création de tache
 */

/**
 * @brief Ajout d'une tâche dans l'ordonnanceur
 *
 * On se contente de l'insérer dans la liste des tâches de l'ordonnanceur. 
 */
void ordonnanceurAddTache(Tache * tache);

/*
TacheID ordonnancerTache(CorpsTache corpsTache, booleen nouvelleConsole);
 * Création d'une nouvelle tâche et mise de celle-ci dans
 * la liste du scheduler. Si nouvelleConsole est vrai, on crée une
 * nouvelle console pour cette tâche. Sinon elle hérite de celle de
 * son créateur.
 */

void ordonnanceur();
/*
 * Basculer vers la prochaine tache à exécuter
 */

int sys_identifiantTache();
/*
 * Obtention du numero de la tache en cours. WARNING ça n'a rien
 * à faire là ...
 */

uint32_t AS_console();
/*
 * Obtention de la console de la tache en cours. WARNING ça n'a rien
 * à faire là ...
 */

int sys_basculerTache(ParametreAS as);
/*
 * Implantation de l'appel système d'invocation de l'ordonnanceur
 */

TacheID sys_creerTache(ParametreAS as, CorpsTache corpsTache, booleen shareConsole);

#endif
