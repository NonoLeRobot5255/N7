/**
 * @brief : exemple de noyau utilisant le journal via l'interface fichiers
 *
 *                                                     (C) Manu Chaput 2000-2023
 */
#include <manux/config.h>
#include <manux/debug.h>
#include <manux/bootloader.h>      // infoSysteme
#include <manux/memoire.h>         // initialiserMemoire
#include <manux/console.h>
#include <manux/printk.h>
#include <manux/fichier.h>
#include <manux/journal.h>
#include <manux/pci.h>
#include <manux/virtio-console.h>

void startManuX()
{
   INoeud  iNoeudConsole;  // Le INoeud qui décrit la console

   INoeud iNoeudVirtioConsole; 
   Fichier fichierVirtioConsole;
   
   // Récupération des informations depuis le bootloader
   bootloaderLireInfo();

   // Initialisation de la console noyau
   consoleInitialisationINoeud(&iNoeudConsole);

   //bootloaderInitialiser();

   initialiserMemoire(infoSysteme.memoireDeBase,
                      infoSysteme.memoireEtendue);

   // Initialisation du journal
   journalInitialiser(&iNoeudConsole);

   // Initialisation du bus PCI
   PCIEnumerationDesEquipements();

   // Initialisation de la console virtio
   if (virtioConsoleInitialisation(&iNoeudVirtioConsole) == 0/*ESUCCES*/) {
     ouvrirFichier(&iNoeudVirtioConsole, &fichierVirtioConsole, O_WRONLY, 0);
      journalAffecterFichier(&fichierVirtioConsole);
   }
   
   // Un petit message
   printk("Printk dit bonjour via le journal !\n");
  
}   /* startManuX */


