/**
 * @file virtio-console.c
 *
 * A faire : la gestion de la mémoire n'est pas terrible ! J'alloue
 * une page pour chaque nouveau message et je la supprime lorsque je
 * récupère les buffers (voir les "WARNING Pas top" dans le
 * code). Idéalement, il vaudrait mieux que ce soit virtio qui gère
 * ça. Par exemple à l'initialisation, je lui dit que je veux qu'il
 * copie les données. Du coup il alloue une première fois les buffers
 * assiociés aux descripteurs, puis il les récupère avec les buffers,
 * sans les libérer/réallouer. Au pire il peut les faire croitre si
 * nécessaire !
 */

#include <manux/virtio-console.h>

#include <manux/intel-8259a.h>  // pour les interruptions 
#include <manux/pci.h>          // Pour aller récupérer l'irq, on doit
				// pouvoir s'en passer avec une
				// fonction dans virtio
#include <manux/memoire.h>      // allouerPages

#include <manux/io.h>           // outb
#include <manux/debug.h>
#include <manux/errno.h>
#include <manux/string.h>

/**
 * Description d'un périphérique virtio console
 */
typedef struct VirtioConsole_t {
   VirtioPeripherique    virtioPeripherique; 
   uint16_t              nbItRecues;
} VirtioConsole;

/**
 * WARNING : pour le moment on crée un unique périphérique
 */
VirtioConsole virtioConsole; 
 static int    nbPageAlloueesIci = 0;

/**
 * Gestion des buffers utilisés par le périphérique
 */
#define NB_BUFF_TRAITES 16
void virtioConsoleTraiterBuffers(VirtioConsole * vc)
{
   void *bf [NB_BUFF_TRAITES];
   int lg[NB_BUFF_TRAITES];
   int nbLu;

   // Récupération d'une éventuelle entrée
   nbLu = virtioFileRecupererBuffers(
	  &(vc->virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_IN]),
			      bf, lg, NB_BUFF_TRAITES);
   //printk("[7] FQ %d\n", nbLu);
   do {
      // Récupération des buffers émis et consommés
      nbLu = virtioFileRecupererBuffers(  
	     &(vc->virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_OUT]),
	     bf, lg, NB_BUFF_TRAITES);
      //printk("[7] OK !\n");

      // WARNING Pas top
      for (int n = 0; n < nbLu; n++) {
	 libererPage(bf[n]);
         nbPageAlloueesIci --;
	 //	 printk("[7] virtioConsoleTraiterBuffers libere page 0x%x (reste %d)\n", bf[n], nbPageAlloueesIci);
      }
   } while (nbLu > 0);
   /*
   printk("[7] Apres lecture ...\n");
   virtioAfficherFile(&(vc->virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_OUT]));
   */
   virtioFileAutoriserInterruption(&(vc->virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_OUT]));
   virtioFileAutoriserInterruption(&(vc->virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_IN]));
				   }

/**
 *  Cf [3] section 2.4.2
 */
void virtioConsoleGestionInt(void * pr)
{
   VirtioConsole * vc = (VirtioConsole *) pr;
   uint8_t isr;

   vc->nbItRecues++;
   printk_debug(DBG_KERNEL_VIRTIO, "Interruption %d !!!\n", vc->nbItRecues);

   // Est-ce moi qui suis visé ?
   inb((uint16_t)(vc->virtioPeripherique.pciEquipement->adresseES + VIRTIO_HIST_ISR), isr);
   if (isr & 0x1) {
      printk_debug(DBG_KERNEL_VIRTIO, "C'est pour moi, ...\n");

      // La suite est à déférer dans une partie basse
      virtioConsoleTraiterBuffers(vc);
   } else {
     printk_debug(DBG_KERNEL_VIRTIO, "Fuck\n");
   }
}


/**
 * @brief Initialisation d'un périphérique console virtio
 *
 */
int virtioConsoleInitPeripherique(int PCINumeroPeripherique)
{
   PCIEquipement       * pciEquip = PCIEquipementNumero(PCINumeroPeripherique);
   void                * pointeur; // Pour allouer de la mémoire en
				   // réception
   VirtioFileVirtuelle * fr;       // réception
   // On va construire un tableau de buffers (et un de leurs
   // longueurs) pour passer à virtioFournirBuffers
   void                * buffers[1];
   int                   longueurs[1];

   printk_debug(DBG_KERNEL_VIRTIO, "IN\n");

   // On renseigne la structure
   virtioInitPeripheriquePCI(&(virtioConsole.virtioPeripherique),
			     PCINumeroPeripherique,
			     VIRTIO_CONSOLE_F_SIZE
	                   | VIRTIO_CONSOLE_F_MULTIPORT);

   // La suite est à mettre dans virtio (ou à virer ?)
   if (i8259aAjouterHandler(pciEquip->interruption,
                            virtioConsoleGestionInt,
			    &virtioConsole)){
      printk(PRINTK_CRITIQUE "Trop de handler sur l'interruption %d\n", pciEquip->interruption);
      paniqueNoyau("Pas possible");
      return ENOENT;
   }
   i8259aAutoriserIRQ(pciEquip->interruption);
   virtioConsole.nbItRecues = 0;
   
   // On ajoute des buffers sur la file d'entrée
   fr = &(virtioConsole.virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_IN]);

   // Pas de malloc, ... WARNING : faire version avec malloc
   pointeur = allouerPages(NB_PAGES(fr->taille*(1024)));

   for (int i = 0 ; i < fr->taille ; i++) {
      buffers[0] = pointeur;
      longueurs[0] = 1024;
      pointeur += longueurs[0];

      virtioFournirBuffers(&(virtioConsole.virtioPeripherique),
			   VIRTIO_CONSOLE_PORT0_IN,
            	           buffers, longueurs,
                           1,
		           VRING_DESC_F_WRITE);
   }

   printk_debug(DBG_KERNEL_VIRTIO, "OUT\n");

   return ESUCCES;
}

#ifdef MANUX_FICHIER
MethodesFichier virtioConsoleMethodesFichier;

/**
 * @brief : fonction d'écriture dans un périphérique virtio-console
 */
size_t virtioConsoleEcrire(Fichier * f, void * b, size_t l)
{
   VirtioConsole * vc = (VirtioConsole *)f->prive;

   void *bf [1];
   int lg[1];
   int nb;

   // On essaie d'aller chercher des buffers WARNING :pas sûr de la logique !
   virtioConsoleTraiterBuffers(vc);

   /*
   printk("[7] Avant ecriture ...\n");
   virtioAfficherFile(&(vc->virtioPeripherique.filesVirtuelles[VIRTIO_CONSOLE_PORT0_OUT]));
   */
   // WARNING Pas top
   bf[0] = allouerPage();
   nbPageAlloueesIci ++;
   //   printk("[7] virtioConsoleTraiterBuffers allouee page 0x%x (donc %d)\n", bf[0], nbPageAlloueesIci);
   
   memcpy(bf[0], b, l);

   lg[0] = l;

   nb = virtioFournirBuffers(&(vc->virtioPeripherique),
			1,
			bf, lg, 1, 0);

   // Un peu simpliste, ...
   if (nb) {
      return l;
   }
   
   return 0;
      
}

/**
 * @brief : fonction de lecture dans un périphérique virtio-console
 */
size_t virtioConsoleLire(Fichier * f, void * b, size_t l)
{
   printk_debug(DBG_KERNEL_VIRTIO, "in\n");

   return 0;
}

int virtioConsoleOuvrir(INoeud * iNoeud, Fichier * f, uint16_t fanions, uint16_t mode)
{
   f->prive = &virtioConsole; // WARNING, il peut y en avoir plusieurs 

   return ESUCCES;
}

/**
 * Les méthodes permettant de traiter une console virtio comme un
 * fichier
 */
MethodesFichier virtioConsoleMethodesFichier = {
   .ouvrir = virtioConsoleOuvrir,
   .lire = virtioConsoleLire,
   .ecrire = virtioConsoleEcrire
};
#endif // MANUX_FICHIER

/**
 * @brief Initialisation des périphériques
 */
int virtioConsoleInitialisation(INoeud * iNoeudVirtioConsole)
{
   int PCINumeroPeripherique;
  
   printk_debug(DBG_KERNEL_VIRTIO, "IN\n");

   // On va chercher un peripherique virtio net
   PCINumeroPeripherique = PCIObtenirProchainEquipement(PCI_VENDEUR_VIRTIO,
							PCI_PERIPHERIQUE_VIRTIO_CONSOLE,
							-1);
   printk_debug(DBG_KERNEL_VIRTIO, "Peripherique PCI %d\n", PCINumeroPeripherique);

   if (PCINumeroPeripherique == -1) {
      return ENOENT;
   }
   
   // Initialisation de l'unique périphérique pour le moment
   if (virtioConsoleInitPeripherique(PCINumeroPeripherique)== 0) {
      printk_debug(DBG_KERNEL_VIRTIO, "Console virtio initialisee !\n");
   }

#ifdef MANUX_FICHIER
   iNoeudVirtioConsole->typePeripherique.majeur = MANUX_VIRTIO_CONSOLE_MAJEUR;
   iNoeudVirtioConsole->typePeripherique.mineur = 0;
   iNoeudVirtioConsole->prive = NULL;
   iNoeudVirtioConsole->methodesFichier = &virtioConsoleMethodesFichier;
#endif
   
   printk_debug(DBG_KERNEL_VIRTIO, "out\n");

   return ESUCCES;
}


