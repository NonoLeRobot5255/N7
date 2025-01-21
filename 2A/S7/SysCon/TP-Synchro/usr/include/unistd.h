/*----------------------------------------------------------------------------*/
/*      Définition des fonctions de base du mode utilisateur de ManuX.        */
/*                                                                            */
/*                                                  (C) Manu Chaput 2002-2021 */
/*----------------------------------------------------------------------------*/
#ifndef _UNISTD_H
#define _UNISTD_H

#include <manux/types.h>

/**
 * @brief Création d"une nouvelle tâche 
 * @param  corps : fonction à exécuter
 * @param  shareCons : partage-t-on la console de la tâche actuelle ?
 * @return le numéro de la tâche créée.
 */
int creerNouvelleTache(void (corps()), booleen shareCons);

/**
 * @brief Basculer vers une autre tâche.
 * On rend simplement la main, c'est du collaboratif.
 */
int basculerTache();

/**
 * @brief Un appel système sans intérêt, pour l'exemple
 */
int appelSystemeInutile();

/**
 * @brief Création d'un tube de communication
 */
int tube(int * fd);

/**
 * @brief Obtention de l'identifiant de la tâche en cours
 */
int identifiantTache();


#endif
