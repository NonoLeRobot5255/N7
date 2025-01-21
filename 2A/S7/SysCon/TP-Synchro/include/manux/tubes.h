/**
 * @file sf/tube.h
 * @brief Définition des tubes de communication
 */
#ifndef TUBES_DEF
#define TUBES_DEF

#include <manux/config.h>

#ifdef MANUX_APPELS_SYSTEME
#   include <manux/appelsysteme.h>
#endif

#ifdef MANUX_APPELS_SYSTEME
/**
 * @brief Implantation de l'appel système tube()
 *
 * On va créer un iNoeud décrivant le tube (une structure en mémoire)
 * puis deux descripteurs de fichiers, l'un pour écrire, l'autre pour
 * lire. 
 */
int sys_tube(ParametreAS as, int * fds);

#endif // MANUX_APPELS_SYSTEME
  
#endif

