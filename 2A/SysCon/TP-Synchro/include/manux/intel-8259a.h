/*----------------------------------------------------------------------------*/
/*      Définition des sous-programmes de gestion du PIC intel 8259A.         */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#ifndef INTEL_8259A
#define INTEL_8259A

#include <manux/types.h>
/*
 * Les ports utilisés pour dialoguer avec les deux PICs
 */
#define PIC_MAITRE_PORT_COMMANDE  0x20
#define PIC_MAITRE_PORT_DONNEE    0x21
#define PIC_ESCLAVE_PORT_COMMANDE 0xA0
#define PIC_ESCLAVE_PORT_DONNEE   0xA1

/*
 * Initialisation du PIC. Le circuit doit être initialisé une fois et
 * une seule au démarrage du système.
 */
void i8259aInit(uint8_t intBase);

/*
 * Ajout d'une fonction de gestion d'un matériel sur une IRQ. Lors
 * d'une interruption, la fonction handler sera invoquée avec le
 * paramètre private.
 *
 * La valeur retournée est
 *   1 en cas de succès, 
 *   0 en cas d'erreur (pour le moment, ManuX ne permet pas de
 *   partager une IRQ)
 */
int i8259aAjouterHandler(int numIRQ, void (*handler)(void *), void * private);

/*
 * Le handler de gestion effective des IRQ. C'est cette fonction qui
 * est invoquée lors d'une interruption matérielle.
 */
void i8259aGestionIRQ(TousRegistres registres, uint32_t numIRQ, 
                      uint32_t eip, uint32_t cs, uint32_t eFlags);

/*
 * Masquage d'une IRQ
 */
void i8259aInterdireIRQ(uint8_t numIRQ);

/*
 * Démasquage d'une IRQ
 */
void i8259aAutoriserIRQ(uint8_t numIRQ);

/*
 * Accusé de réception d'une IRQ
 */
void i8259aAckIRQ(uint8_t numIRQ);

#endif
