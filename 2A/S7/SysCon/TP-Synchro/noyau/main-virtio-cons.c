/**
 * @file :
 * @brief : Un exemple de début de noyau.
 *                                                                            
 *                                                     (C) Manu Chaput 2000-2023
 **/
#include <manux/config.h>
#include <manux/debug.h>
#include <manux/bootloader.h>
#include <manux/errno.h>
#include <manux/console.h>
#include <manux/memoire.h>
#include <manux/interruptions.h>
#include <manux/pci.h>
#include <manux/fichier.h>
#include <manux/virtio-console.h>

#define NB_LIGNES 1280
void testerVirtioConsole(Fichier * f)
{
   printk("On commence ...\n");
   for (int n = 0; n < NB_LIGNES; n++) {
     fprintk(f, "(%d) Une ligne de texte ...\n", n);
   }
   printk("Et voila !\n");
}

void startManuX()
{
   INoeud iNoeudVirtioConsole;
   Fichier fichierVirtioConsole;
   
   // Récupération des informations depuis le bootloader
   bootloaderLireInfo();
   
   // Initialisation de la console noyau
   consoleInitialisation();

   bootloaderInitialiser();

   /* Initialisation de la gestion mémoire */
   initialiserMemoire(infoSysteme.memoireDeBase,
		      infoSysteme.memoireEtendue);
   
   /* Initilisation des descripteurs de segments */
   initialiserGDT();

   /* Initialisation de la table des interruptions */
   initialiserIDT();   

   /* Initialisation du bus PCI */
   printk_debug(DBG_KERNEL_START, "Initialisation du bus PCI ...\n");
   PCIEnumerationDesEquipements();
   printk_debug(DBG_KERNEL_START, "Bus PCI initialise...\n");

   printk_debug(DBG_KERNEL_START, "Initialisation de virtio console ...\n");
   if (virtioConsoleInitialisation(&iNoeudVirtioConsole) == ESUCCES) {
     ouvrirFichier(&iNoeudVirtioConsole, &fichierVirtioConsole, O_WRONLY, 0);
   }
   printk_debug(DBG_KERNEL_START, "Virtio console initialise...\n");


   // Initialisation de la gestion des systèmes de fichiers
   printk_debug(DBG_KERNEL_START, "Initialisation du systeme de fichiers ...\n");
   sfInitialiser();
   printk_debug(DBG_KERNEL_START, "Systeme de fichiers initialise\n");

   testerVirtioConsole(&fichierVirtioConsole);

   while(1){}; // WARNING : faire une fonction d'attente de vidage de
	       // virtio !
   
}   /* startManuX */


