/**----------------------------------------------------------------------------
 * @file periph-car.h
 * @brief définition des périphériques orientés caractère
 *
 *                                                  (c) Manu Chaput 2000-2023
 *----------------------------------------------------------------------------*/
#ifndef __PERIPH_CAR
#define __PERIPH_CAR

#include <manux/types.h>
#include <manux/fichier.h>

typedef struct _peripheriqueCaractere {
   int numero ; // Ce sera un numéro d'inode un jour
   size_t (* lire)(Fichier *, char *, size_t);
   size_t (* ecrire)(Fichier *, char *, size_t);
} PeripheriqueCaractere;
  
#endif
