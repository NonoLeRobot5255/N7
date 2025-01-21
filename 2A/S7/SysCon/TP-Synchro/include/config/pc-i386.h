/*============================================================================*/
/*   Définitions liées au processeur.                                         */
/*============================================================================*/
/**
 * Utilise-t-on des spécificité i386 ?
 */
#define MANUX_LIBI386

/*----------------------------------------------------------------------------*/
/*   Configuration des interruptions                                          */ 
/*----------------------------------------------------------------------------*/
/**
 * Le nombre d'exceptions : 32 sur intel.
 */
#ifndef MANUX_NB_EXCEPTIONS
#   define MANUX_NB_EXCEPTIONS 32
#endif

/**
 * Le nombre total d'interruptions : 256 sur Intel.
 */
#ifndef MANUX_NB_INTERRUPTIONS
#   define MANUX_NB_INTERRUPTIONS 256
#endif

/**
 * Premier numéro d'interruption utilisé pour repositionner les IRQs.
 * On les place derrière les exceptions.
 */
#ifndef MANUX_INT_BASE_IRQ
#   define MANUX_INT_BASE_IRQ MANUX_NB_EXCEPTIONS
#endif

/**
 * Choix du PIC
 */
#ifndef MANUX_PIC
#   define MANUX_PIC INTEL_8259A
#endif

#if (MANUX_PIC == INTEL_8259A)
#   include "config/intel-8259a.h"
#else
#   error "Pas de PIC !?"
#endif

/**
 * @brief Décompte des interruptions
 */
#define MANUX_INT_AUDIT

/*
 * Les IRQ des matériels pris en charge
 */
#define IRQ_HORLOGE   0
#define IRQ_CLAVIER   1
