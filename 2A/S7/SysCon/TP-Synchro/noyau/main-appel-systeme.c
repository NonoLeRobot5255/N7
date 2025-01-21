/*----------------------------------------------------------------------------*/
/*      Un exemple pitoyable de début de noyau.                               */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2023 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>
#include <manux/console.h>
#include <manux/printk.h>
#include <manux/interruptions.h>
#include <manux/intel-8259a.h>

extern void init();

void startManuX()
{
   // Initialisation de la console noyau
   consoleInitialisation();

   // Initialisation de la table des interruptions
   initialiserIDT();   

   i8259aInit(MANUX_INT_BASE_IRQ);
   
   initialiserAppelsSysteme();
   
   // Un petit message
   printk("Printk dit bonjour !\n");

   init();
}   /* startManuX */


