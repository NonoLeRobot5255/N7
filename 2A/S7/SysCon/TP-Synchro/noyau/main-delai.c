/**
 *      Test et calibrage des fonctions de délai.
 *
 *                                                     (C) Manu Chaput 2000-2023
 */
#include <manux/config.h>
#include <manux/interruptions.h>
#include <manux/intel-8259a.h>
#include <manux/console.h>
#include <manux/printk.h>

#define NB_CYCLES     10
#define NB_PAUSES     500
#define DUREE_ATTENTE 20

void startManuX()
{
  uint32_t n, d, f, c;
  
   // Initialisation de la console noyau
   consoleInitialisation();

   // Initilisation des descripteurs de segments 
   initialiserGDT();

   // Initialisation de la table des interruptions
   initialiserIDT();   

   // Initialisation de la table des interruptions
   initialiserIDT();   

   i8259aInit(MANUX_INT_BASE_IRQ);

   // Affichage d'un message
   printk("Prenons un peu de temps ...\n");

   // Initlisation de l'horloge
   initialiserHorloge();
   printk("Horloge initialisee\n");

   for (c = 0; c < NB_CYCLES; c++) {
      d = nbTopHorloge;
      for (n = 0 ; n < NB_PAUSES; n++) {
         attenteMilliSecondes(DUREE_ATTENTE);
      }
      f = nbTopHorloge;
   
      printk("Fin de l'exercice d=%d, f=%d => %d ms...\n", d, f, (f-d)*1000/MANUX_FREQUENCE_HORLOGE);
   }
}   /* _startManuX */

