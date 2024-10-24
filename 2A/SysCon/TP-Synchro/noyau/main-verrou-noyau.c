/**
 * @file :
 * @brief : Un exemple de début de noyau.
 *                                                                            
 *                                                     (C) Manu Chaput 2000-2023
 **/
#undef MANUX_RAMDISK

#include <manux/config.h>
#include <manux/bootloader.h>
#include <manux/errno.h>
#include <manux/console.h>
#include <manux/clavier.h>
#include <manux/tache.h>
#include <manux/horloge.h>        // initialiserHorloge
#include <manux/scheduler.h>
#include <manux/interruptions.h>
#include <manux/io.h>
#include <manux/segment.h>
#include <manux/memoire.h>
#include <manux/atomique.h>
#include <manux/appelsysteme.h>
#include <manux/printk.h>
#include <manux/debug.h>
#include <manux/segment.h>
#include <manux/pagination.h>
#include <manux/limites.h>

extern void init(); // Faire un init.h

/**
 * Configuration de la console
 */
INoeud  iNoeudConsole;  // Le INoeud qui décrit la console

void startManuX()
{
   union {
      uint32_t registres[3];
      char     caracteres[13];
   } descriptionProc;

   // Récupération des informations depuis le bootloader
   bootloaderLireInfo();
   
   // Initialisation de la console noyau
   consoleInitialisation();

   bootloaderInitialiser();
      
   // Lecture du nom du processeur
   descriptionProcesseur(0, descriptionProc.registres);
   descriptionProc.caracteres[12] = 0;

   // Affichage du premier message
   printk_debug(DBG_KERNEL_START, "32 bit ManuX running on a '%s' ...\n",
		descriptionProc.caracteres);

   // Affichage de la mémoire disponible 
   printk_debug(DBG_KERNEL_START, "Memoire : %d + %d Ko\n",
		infoSysteme.memoireDeBase,
		infoSysteme.memoireEtendue);

   /* Initialisation de la gestion mémoire */
   printk_debug(DBG_KERNEL_START, "Initialisation memoire ...\n");
   initialiserMemoire(infoSysteme.memoireDeBase,
		      infoSysteme.memoireEtendue);
   
   /* Initilisation des descripteurs de segments */
   initialiserGDT();

   /* Initialisation de la table des interruptions */
   initialiserIDT();   

   /* Initialisation de la pagination */
   printk_debug(DBG_KERNEL_START, "Initialisation pagination ...\n");
   initialiserPagination(infoSysteme.memoireEtendue);
   printk_debug(DBG_KERNEL_START, "Pagination initialisee\n");
   
   /* Initialisation de la table des appels système*/
   printk_debug(DBG_KERNEL_START, "Initialisation appels systeme ...\n");
   initialiserAppelsSysteme();
   printk_debug(DBG_KERNEL_START, "Appels systeme initialises\n");
  
   // Initialisation du clavier
   printk_debug(DBG_KERNEL_START, "Initialisation du clavier ...\n");
   initialiserClavier();
   printk_debug(DBG_KERNEL_START, "Clavier initalise\n");

   printk_debug(DBG_KERNEL_START, "Initialisation de l'horloge ...\n");
   initialiserHorloge();
   printk_debug(DBG_KERNEL_START, "Horloge initialisee\n");

   // Initialisation de la gestion des processus
   printk_debug(DBG_KERNEL_START, "Initialisation du scheduler ...\n");
   initialiserScheduler();
   printk_debug(DBG_KERNEL_START, "Scheduler initialise\n"); 

   // On va maintenant faire de la tâche en cours une tâche "banale"
   tacheSetConsole(tacheEnCours, creerConsoleVirtuelle());

   init();
}   /* startManuX */


