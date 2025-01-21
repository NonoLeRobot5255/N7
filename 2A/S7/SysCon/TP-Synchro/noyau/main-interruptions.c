/*----------------------------------------------------------------------------*/
/*      Un exemple pitoyable de début de noyau.                               */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2023 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>
#include <manux/console.h>
#include <manux/printk.h>
#include <manux/interruptions.h>

void startManuX()
{
   int a, b = 0;
   
   // Initialisation de la console noyau
   consoleInitialisation();

   // Initilisation des descripteurs de segments 
   initialiserGDT();

   // Initialisation de la table des interruptions
   initialiserIDT();   

   // Un petit message
   printk("ManuX et les interruptions ...\n");

   // On déclanche une exception "division par zéro"
   a = 1/b;
   
   printk("Ciao ...\n");
   
}   /* startManuX */
