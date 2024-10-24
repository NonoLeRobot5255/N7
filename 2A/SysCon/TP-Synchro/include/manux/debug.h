/*----------------------------------------------------------------------------*/
/*      Ma version des assertions et autres outils de debug.                  */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2023 */
/*----------------------------------------------------------------------------*/
#ifndef MANUX_DEBUG_DEF
#define MANUX_DEBUG_DEF

#include <manux/config.h>
#include <manux/printk.h>
#include <manux/stdarg.h>
#include <manux/scheduler.h>     // tacheEnCours
#ifdef MANUX_LIBI386
#   include <manux/i386.h>       // halt()
#   include <manux/horloge.h>    // nbTopHorloge
#endif


#define DBG_KERNEL_ERREUR     0x00000001
#define DBG_KERNEL_START      0x00000002
#define DBG_KERNEL_PAGIN      0x00000004
#define DBG_KERNEL_SYSFI      0x00000008
#define DBG_KERNEL_ORDON      0x00000010
#define DBG_KERNEL_TACHE      0x00000020
#define DBG_KERNEL_MEMOIRE    0x00000040
#define DBG_KERNEL_AS         0x00000080
#define DBG_KERNEL_PCI        0x00000100
#define DBG_KERNEL_NET        0x00000200
#define DBG_KERNEL_VIRTIO     0x00000400
#define DBG_KERNEL_A_FAIRE    0x00000800
#define DBG_KERNEL_BOOTLOADER 0x00001000
#define DBG_KERNEL_TUBE       0x00002000
#define DBG_KERNEL_ALL        0xFFFFFFFF

#define masqueDebugageConsole (0x00000000 \
 | DBG_KERNEL_START      \
			       )
#define masqueDebugageFichier (0x00000000\
			       )
/*
 | DBG_KERNEL_ERREUR     \
 | DBG_KERNEL_START      \
 | DBG_KERNEL_PAGIN      \
 | DBG_KERNEL_MEMOIRE    \
 | DBG_KERNEL_TACHE      \
 | DBG_KERNEL_ORDON      \
 | DBG_KERNEL_ALL        \
 | DBG_KERNEL_AS         \
 | DBG_KERNEL_SYSFI      \
 | DBG_KERNEL_TUBE       \
*/

/**
 * Une fonction permettant d'afficher des messages de debug thématiques
 * et avec un formatage homogène.
 */
#ifdef MANUX_LIBI386  // pour les tops horloge
#define printk_debug(lvl, fmt, args...)	 \
   if (((lvl)& masqueDebugageConsole) && ((lvl)& masqueDebugageFichier)) {     \
      printk("{7} [%d] %s line %d : " fmt, nbTopHorloge, __FUNCTION__ , __LINE__, ## args); \
   } else if ((lvl)& masqueDebugageFichier) {				\
      printk("(7) [%d] %s line %d : " fmt, nbTopHorloge, __FUNCTION__ , __LINE__, ## args); \
   } else if ((lvl)& masqueDebugageConsole) {				\
      printk("[7] [%d] %s line %d : " fmt, nbTopHorloge, __FUNCTION__ , __LINE__, ## args); \
   }
#else
#define printk_debug(lvl, fmt, args...)	 \
   if (((lvl)& masqueDebugageConsole) && ((lvl)& masqueDebugageFichier)) {     \
      printk("{7} %s line %d : " fmt, __FUNCTION__ , __LINE__, ## args); \
   } else if ((lvl)& masqueDebugageFichier) {				\
      printk("(7) %s line %d : " fmt, __FUNCTION__ , __LINE__, ## args); \
   } else if ((lvl)& masqueDebugageConsole) {				\
      printk("[7] %s line %d : " fmt, __FUNCTION__ , __LINE__, ## args); \
   }
#endif
/*
 * Affichage d'un message de panique
 */
#ifdef MANUX_TACHES
#define paniqueNoyau(fmt, args...)	                                  \
  { 								\
   printk("\n*** PANIQUE NOYAU (tache %d) ***\n", tacheEnCours->numero); \
   printk("%s (dans %s ligne %d)\n", __FUNCTION__, __FILE__, __LINE__);   \
   printk("" fmt, ## args);                                               \
   asm( "hlt" );                                                          \
}
#else
#define paniqueNoyau(fmt, args...)	                                  \
{\
   printk("\n*** PANIQUE NOYAU  ***\n");					\
   printk("%s (dans %s ligne %d)\n", __FUNCTION__, __FILE__, __LINE__);   \
   printk("" fmt, ## args);                                               \
   asm( "hlt" ); \
}
#endif

/*
 * Ma version simplifiée de assert
 */
#ifdef MANUX_ASSERT_ACTIVES
#define assert(cond)     \
  if (!(cond)) {					      \
    paniqueNoyau("L'assertion '"#cond"' n'est pas verifiee"); \
  }

#else
#define assert(cond) {}
#endif

#endif
