/*----------------------------------------------------------------------------*/
/*      Implémentation des sous-programmes de gestion de l'horloge matérielle.*/
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>
#include <manux/debug.h>
#include <manux/intel-8259a.h>
#include <manux/horloge.h>
#include <manux/io.h>           // outb
#include <manux/memoire.h>      // NULL
#ifdef MANUX_TACHES
#   include <manux/scheduler.h>    // ordonnanceur
#endif
#include <manux/printk.h>

/*
 * Nous allons décompter avec cette variable le nombre d'interruptions d'horloge
 */
Temps nbTopHorloge = 0;

/*
 * Le calibre pour les attentes courtes actives
 */
uint32_t attenteCalibre;

/*
 * Le handler du timer
 */
void handlerHorloge(void * inutile)
{
   nbTopHorloge++;

#if defined(MANUX_TACHES) && defined(MANUX_PREEMPTIF) 
   if (tacheEnCours) {
      ordonnanceur();
   }
#endif
}

/*
 * Configuration de la fréquence du circuit
 */ 
void setFrequenceHorloge(uint16_t freqHz)
{
   uint16_t decompte;

   decompte = 1193200 / freqHz;

   // On initialise la fréquence du timer 0 WARNING a rendre plus propre
   outb(0x43, 0x34); // Was 36
   outb(0x40, decompte & 0xFF);
   outb(0x40, (decompte >> 8) & 0xFF);
}

/**
 * @brief Calibrage de la fonction mdelay()
 */
void __attribute__((optimize("O0"))) attenteCalibrer()
{
   Temps    t;
   uint32_t n = 0;

   t = nbTopHorloge;
   
   // On attend le prochain top
   do {
   } while (t == nbTopHorloge);
   t += 1 + MANUX_NB_CYCLES_CALIBRAGE;
   
   // On compte le nombre de boucles entre deux tops
   do {
      n++;
   } while (nbTopHorloge < t);

   // On a donc fait n boucles entre deux tops soit une durée de
   // 1000*NB_CYCLES_CALIBRAGE/MANUX_FREQUENCE_HORLOGE ms. Donc pour
   // une milliseconde il nous faut 
   attenteCalibre = ((MANUX_FREQUENCE_HORLOGE/MANUX_NB_CYCLES_CALIBRAGE) * n)/1000;

   //printk("Calibrage : n = %d, f = %d, c = %d\n", n, MANUX_FREQUENCE_HORLOGE, attenteCalibre);
}

/** 
 * @brief Initialisation du système d'horloge
 */
void initialiserHorloge()
{

   // Initialisation de la fréquence de l'horloge matérielle
   setFrequenceHorloge(MANUX_FREQUENCE_HORLOGE);

   // Enregistrement auprès du PIC
   i8259aAjouterHandler(IRQ_HORLOGE, handlerHorloge, NULL);

   // Autorisation de l'IRQ
   i8259aAutoriserIRQ(IRQ_HORLOGE);

   // Calibrage du système d'attente active
   attenteCalibrer();
}

/**
 * @brief Attente active de n millisecondes
 */
void __attribute__((optimize("O0"))) attenteMilliSecondes(int n)
{
   uint32_t m = n * attenteCalibre;
   uint32_t c = 0;

   do {
      c++;
   } while (c < m);
}

