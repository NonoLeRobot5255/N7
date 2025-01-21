/*----------------------------------------------------------------------------*/
/*      Implémentation des sous-programmes de gestion du PIC intel 8259A.     */
/*                                                                            */ 
/* On suppose ici une architecture de type PC-AT, avec deux PICs en cascade   */
/*                                                                            */ 
/* Voir https://wiki.osdev.org/PIC                                            */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>

#include <manux/memoire.h>      // NULL
#include <manux/io.h>
#include <manux/types.h>
#include <manux/errno.h>

#include <manux/interruptions.h> // nbItRecues
#include <manux/intel-8259a.h>

/**
 * @brief Structure permettant de définir un matériel "client"
 */
typedef struct {
   void (* handler)(void *);
   void * private;;
} i8259aClient;

/**
 * Tableau des handlers et data
 */
i8259aClient handlerClients[I8259A_NB_IRQ][MANUX_NB_HANDLER_PAR_IRQ];

/**
 * Nombre de handlers enregistrés par IRQ
 */
int nbHandlerClients[I8259A_NB_IRQ];

/*
 * Quelques macros utiles 
 */
#define PIC_EOI 0x20        // Confirmation d'une interruption

// Premier mot de configuration
#define ICW1_INIT     0x10   // Initialisation
#define ICW1_ICW4     0x01   // Config en 4 mots

// Troisième mot de configuration
#define ICW3_ESCLAVE2 0x02   // Pour un esclave sur IRQ2
#define ICW3_MAITRE2  0x04   // Pour un maître avec une cascade sur IRQ2

// Quatrième mot de configuration
#define ICW4_8086     0x01   // Config de base (x86)

// WARNING pas l'idéal !
#define delaiOutB {for(int __x = 0; __x<20; __x++){asm("");}}
/*
 * Initialisation des PICs.
 *
 * intBase stipule le numéro d'interruption correspondant à l'IRQ 0 du maître.
 * pour l'esclave, c'est en suivant (donc intBase + 8).
 */
void i8259aInit(uint8_t intBase)
{
   uint8_t m, s;
   int i;

   // On sauve les masques 
   inb(PIC_MAITRE_PORT_DONNEE, m);
   inb(PIC_ESCLAVE_PORT_DONNEE, s);

   // On envoie les 4 mots d'initialisation au maître

   // Premier mot ICW1 : initialisation (ICW1_INIT) en 4 mots (ICW1_ICW4)
   outb(PIC_MAITRE_PORT_COMMANDE, ICW1_INIT | ICW1_ICW4);
   delaiOutB;

   // Deuxième mot : la base des INT
   outb(PIC_MAITRE_PORT_DONNEE, intBase);
   delaiOutB;

   // Troisième mot : le second est en cascade sur IRQ 2
   outb(PIC_MAITRE_PORT_DONNEE, ICW3_MAITRE2);
   delaiOutB;
   
   // Quatrième mot : config de base
   outb(PIC_MAITRE_PORT_DONNEE, ICW4_8086);
   
   // Premier mot ICW1 : initialisation (ICW1_INIT) en 4 mots (ICW1_ICW4)
   outb(PIC_ESCLAVE_PORT_COMMANDE, ICW1_INIT | ICW1_ICW4);
   delaiOutB;

   // Deuxième mot : la base des INT
   outb(PIC_ESCLAVE_PORT_DONNEE, intBase + 8);
   delaiOutB;

   // Troisième mot :il est en cascade du maître
   outb(PIC_ESCLAVE_PORT_DONNEE, ICW3_ESCLAVE2);
   delaiOutB;
   
   // Quatrième mot : config de base
   outb(PIC_ESCLAVE_PORT_DONNEE, ICW4_8086);
   delaiOutB;

   // On restaure les masques
   outb(PIC_MAITRE_PORT_DONNEE, m);//|0xff);
   outb(PIC_ESCLAVE_PORT_DONNEE, s);//|0xff);

   // On met à NULL les handlers
   for (i = 0; i < I8259A_NB_IRQ; i++) {
      nbHandlerClients[i] = 0;
      //      handlerClients[i].handler = (void (*)(void *)) NULL;
      //      handlerClients[i].private = NULL;
   }
}

/**
 * @brief Ajout d'un handler
 */
int i8259aAjouterHandler(int numIRQ, void (*handler)(void *), void * private)
{
   // On ne gère que un handler par IRQ
   if (nbHandlerClients[numIRQ] >= MANUX_NB_HANDLER_PAR_IRQ) {
      return ENOMEM;
   }

   handlerClients[numIRQ][nbHandlerClients[numIRQ]].handler = handler;
   handlerClients[numIRQ][nbHandlerClients[numIRQ]].private = private;

   nbHandlerClients[numIRQ] ++;
   
   return ESUCCES;
}

/**
 * Masquage d'une IRQ
 */
void i8259aInterdireIRQ(uint8_t numIRQ)
{
   char masque;
   uint16_t port = PIC_MAITRE_PORT_DONNEE;
   
   // Circuit esclave (0x0f > numIRQ >= 0x08) ?
   if (numIRQ & 0x08) {
      port = PIC_ESCLAVE_PORT_DONNEE;
      numIRQ &= 0x07;   // On ne garde que les 3 derniers bits
   }
   
   // On lit le masque actuel
   inb(port, masque);

   // On positionne le masque modifié
   outb(port, masque & (0x01 << numIRQ));
}

/**
 * @brief Masquage d'une IRQ
 */
void i8259aAutoriserIRQ(uint8_t numIRQ)
{
   char masque;
   uint16_t port = PIC_MAITRE_PORT_DONNEE;
   
   // Circuit esclave (0x0f > numIRQ >= 0x08) ?
   if (numIRQ & 0x08) {
      port = PIC_ESCLAVE_PORT_DONNEE;
      numIRQ &= 0x07;   // On ne garde que les 3 derniers bits
   }
   
   // On lit le masque actuel
   inb(port, masque);

   // On positionne le masque modifié
   outb(port, masque & ~(0x01 << numIRQ));
}

/**
 * @brief Accusé de réception d'une IRQ
 *
 * Note : on envoie ici un EOI non spécifique (cf [5] p 15) alors que
 * Linux semble faire du specifique.
 */
void i8259aAckIRQ(uint8_t numIRQ)
{
   // Si c'est suite à une interruption de l'esclave il faut *aussi*
   // prévenir le maître (cascade)
   if (numIRQ & 0x08) {
      outb(PIC_ESCLAVE_PORT_COMMANDE, PIC_EOI);
   }
   outb(PIC_MAITRE_PORT_COMMANDE, PIC_EOI);
}

/**
 * @brief Le handler de gestion effective des IRQ.
 *
 * C'est cette fonction qui est invoquée lors d'une interruption matérielle.
 */
void i8259aGestionIRQ(TousRegistres registres, uint32_t numIRQ, 
                      uint32_t eip, uint32_t cs, uint32_t eFlags)
{
   int i;

#ifdef MANUX_INT_AUDIT
   nbItRecues[numIRQ] ++;
#endif
   
   // On accuse réception auprès du PIC
   i8259aAckIRQ(numIRQ);

   // On invoque les handlers de tous les clients
   for (i = 0 ; i < nbHandlerClients[numIRQ]; i++) {
      if (handlerClients[numIRQ][i].handler) {
         handlerClients[numIRQ][i].handler(handlerClients[numIRQ][i].private);
      }
   }
}
