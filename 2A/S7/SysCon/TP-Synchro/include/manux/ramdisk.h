/*----------------------------------------------------------------------------*/
/*      Définition de RamDisk pour Manux.                                     */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef RAMDISK_DEF
#define RAMDISK_DEF

#include <manux/types.h>

void initialiserRamDisk(uint32_t adresse, uint16_t tailleKo);
/*
 * Prise en compte d'un ramdisk chargé par l'init et dont la taille
 * est fournie. L'adresse de départ (fournie) est telle que le ramdisk
 * occupe les tailleKo derniers Ko de la RAM.
 */

#endif
