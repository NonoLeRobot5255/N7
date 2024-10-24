/**---------------------------------------------------------------------------*/
/* @file : clavier.c                                                          */
/* @brief: Implantation des sous-programmes de manipulation du clavier.       */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2023 */
/*----------------------------------------------------------------------------*/
#include <manux/clavier.h>

#include <manux/io.h>
#include <manux/intel-8259a.h>
#include <manux/printk.h>
#include <manux/interBasNiveau.h>
#include <manux/memoire.h>           // NULL
#include <manux/scheduler.h>         // basculeConsoleDemandee

#ifdef MANUX_CLAVIER_CONSOLE
#   include <manux/console.h>
#endif

#include <keymaps/french.h>

/*
 * Description de l'état courant du clavier
 */
int codeClavier = 0; // Code de la dernière touche manipulée
int shiftActif  = 0;

void handlerClavier(void * toto);

void initialiserClavier()
{
   codeClavier = 0;

   i8259aInterdireIRQ(IRQ_CLAVIER);

   // On s'enregistre auprès du PIC
   i8259aAjouterHandler(IRQ_CLAVIER, handlerClavier, NULL);
   
   /* Activation du clavier */
   outb(portDonneesClavier, 0xf4);
   outb(portCmdClavier, 0xae);

   i8259aAutoriserIRQ(IRQ_CLAVIER);
}

#define KEYCODE_ESC  0x01
#define KEYCODE_TAB  0x0F
#define KEYCODE_F1   0x3b
#define KEYCODE_F2   0x3c
#define KEYCODE_F3   0x3d
#define KEYCODE_F4   0x3e
#define KEYCODE_F5   0x3f
#define KEYCODE_F6   0x40
#define KEYCODE_F7   0x41
#define KEYCODE_F8   0x42
#define KEYCODE_F9   0x43
#define KEYCODE_F10  0x44

#define SC_SHIFT_GAUCHE 0x2a

/*
 * Le handler du clavier. Il n'a pas besoin de paramêtre
 */
void handlerClavier(void * toto)
{
   uint8_t etat;

   inb(0x64, etat);

   if (etat & 0x01) {
      inb(0x60, codeClavier);
      codeClavier &= 0xFF;

      // Gestion des shifts
      if (codeClavier == SC_SHIFT_GAUCHE) {
         shiftActif++;
	 return;
      }
      if (codeClavier == (SC_SHIFT_GAUCHE | 0x80)) {
         shiftActif--;
	 return;
      }
      // printk("[KBD-0x%x / %d]\n", codeClavier, shiftActif);
      
#ifdef MANUX_CONSOLES_VIRTUELLES
      if (codeClavier == KEYCODE_ESC) {
         basculeConsoleDemandee = TRUE;
	 return;
      }
#endif

#ifdef MANUX_TACHES
      if (codeClavier == KEYCODE_F1) {
 	 basculerTacheDemande = TRUE;
	 return;
      }
#endif
#ifdef MANUX_CLAVIER_CONSOLE
      Console * cons;
#   ifdef MANUX_CONSOLES_VIRTUELLES
      cons = consoleActive;
#   else
      cons = consoleNoyau();
#   endif

      if (codeClavier & 0x80) {
	printk("(up)\n");
      } else {
         if (cons->bufferClavier){ 
            if (cons->nbCarAttente < 4096) {
               cons->bufferClavier[(cons->indiceProchainCar + cons->nbCarAttente)%4096] =
		 shiftActif ?keymapShift[codeClavier]:keymap[codeClavier];
	       cons->nbCarAttente++;
	    }
	 }
      }
#endif
   }
}
