/**
 * @brief : exemple de noyau utilisant le journal
 *
 *                                                     (C) Manu Chaput 2000-2023
 */
#include <manux/config.h>
#include <manux/console.h>
#include <manux/printk.h>
#include <manux/journal.h>

void startManuX()
{
   // Initialisation de la console noyau
   consoleInitialisation();

   // Initialisation du journal
   journalInitialiser();
   
   // Un petit message
   printk("Printk dit bonjour via le journal !\n");
  
}   /* startManuX */


