
/*----------------------------------------------------------------------------*/
/* Gestion du RAMdisk.                                                        */ 
/*----------------------------------------------------------------------------*/
/*
 * Utilisation d'un RAMdisk ou non
 */
#define MANUX_RAMDISK

/*
 * Sa taille. WARNING : à calculer par un outils comme la taille du noyau
 */
#ifndef MANUX_NB_SECT_RAMDISK
#   define MANUX_NB_SECT_RAMDISK 0x2
#endif

#ifndef MANUX_SEGMENT_TRANSIT_RAMDISK
#   define MANUX_SEGMENT_TRANSIT_RAMDISK 0x4000
#endif

#ifndef MANUX_PREMIER_SECT_RAMDISK 
#   define MANUX_PREMIER_SECT_RAMDISK 0x10
#endif

