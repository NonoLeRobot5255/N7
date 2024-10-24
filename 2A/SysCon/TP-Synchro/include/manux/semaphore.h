/*----------------------------------------------------------------------------*/
/*      Définition des sémaphores et opértions associées.                     */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef SEMAPHORE_DEF
#define SEMAPHORE_DEF

#include <manux/types.h>
#include <manux/atomique.h>
#include <manux/listetaches.h>

/*
 * Le type de base
 */
typedef struct _Semaphore {
  int        valeur;
  Atomique   verrou;
  ListeTache tachesEnAttente;
} Semaphore;

void semInit(Semaphore * sem, int val);
/*
 * Définition de la valeur initiale d'un sémaphore
 */

void semObtenir(Semaphore * sem);
/*
 * Obtention d'une ressource. Cette opération est bloquante.
 */

void semRelacher(Semaphore * sem);
/*
 * Remise au système d'une ressource préalablement obtenue.
 */

#endif
