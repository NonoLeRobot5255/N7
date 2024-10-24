/**
 * @file virtio-net.c
 *
 */
#include <manux/virtio-net.h>
#include <manux/memoire.h>      // allouerPages
#include <manux/intel-8259a.h>  // pour les interruptions 
#include <manux/pci.h>          // Pour aller récupérer l'irq, on doit
				// pouvoir s'en passer avec une
				// fonction dans virtio
#include <manux/io.h>           // outb
#include <manux/debug.h>
#include <manux/errno.h>

// La taille des buffers utilisés par virtio réseau
#ifndef VIRTIO_TAILLE_TRAME_MAX
#   define VIRTIO_TAILLE_TRAME_MAX   2000
#endif

#define VR_FILE_RECEPTION 0
#define VR_FILE_EMISSION  1

/**
 * Les caractéristiques spécifiques au réseau
 */
#define VIRTIO_NET_F_CSUM                   0x00000001   //  0
#define VIRTIO_NET_F_GUEST_CSUM             0x00000002   //  1
#define VIRTIO_NET_F_CTRL_GUEST_OFFLOADS    0x00000004   //  2
#define VIRTIO_NET_F_MAC                    0x00000020   //  5
#define VIRTIO_NET_F_GUEST_TSO4             0x00000080   //  7
#define VIRTIO_NET_F_GUEST_TSO6             0x00000100   //  8
#define VIRTIO_NET_F_GUEST_ECN              0x00000200   //  9
#define VIRTIO_NET_F_GUEST_UFO              0x00000400   // 10
#define VIRTIO_NET_F_HOST_TSO4              0x00000800   // 11
#define VIRTIO_NET_F_HOST_TSO6              0x00001000   // 12
#define VIRTIO_NET_F_HOST_ECN               0x00002000   // 13
#define VIRTIO_NET_F_HOST_UFO               0x00004000   // 14
// Le pilote sait fusionner les buffers
#define VIRTIO_NET_F_MRG_RXBUF              0x00008000   // 15
#define VIRTIO_NET_F_STATUS                 0x00010000   // 16
#define VIRTIO_NET_F_CTRL_VQ                0x00020000   // 17
#define VIRTIO_NET_F_CTRL_RX                0x00040000   // 18
#define VIRTIO_NET_F_CTRL_VLAN              0x00080000   // 19 
#define VIRTIO_NET_F_GUEST_ANNOUNCE         0x00200000

/**
 * Description d'un périphérique virtio net
 */
typedef struct VirtioReseau_t {
   VirtioPeripherique    virtioPeripherique; 
   uint16_t              nbItRecues;
   // Les éléments ci dessous sont sûrement à mettre dans une
   // structure liée au réseau
   uint8_t               adresseMAC[6];
} VirtioReseau;

/**
 * @brief Description de l'entête ajouté par virtio net
 */
typedef struct __attribute__((__packed__)) _VirtioReseauEntete {
   uint8_t   flags; 
   uint8_t   typeGSO;
   uint16_t  longueurEntete;
   uint16_t  tailleGSO;
   uint16_t  debutSommeControle;
   uint16_t  decalageSommeControle;
  //uint16_t  nombreBuffers;  (si on gère VIRTIO_NET_F_MRG_RXBUF)
} VirtioReseauEntete;

/**
 * WARNING : pour le moment on crée un unique périphérique
 */
VirtioReseau virtioReseau; 

/**
 * WARNING : Une affreuse trame ARP requete
 */
VirtioReseauEntete virtioReseauEntete;

uint8_t requeteARP[] = {
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc0, 0xff,
      0xee, 0xde, 0xad, 0xbe, 0x08, 0x06, 0x00, 0x01,
      0x08, 0x00, 0x06, 0x04, 0x00, 0x01, 0xc0, 0xff,
      0xee, 0xde, 0xad, 0xbe, 0x0a, 0x00, 0x02, 0x0f,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a, 0x00,
      0x02, 0x02
   };
uint8_t requeteARP2[] = {
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xc0, 0xff,
      0xee, 0xde, 0xad, 0xbe, 0x08, 0x06, 0x00, 0x01,
      0x08, 0x00, 0x06, 0x04, 0x00, 0x01, 0xc0, 0xff,
      0xee, 0xde, 0xad, 0xbe, 0x0a, 0x00, 0x02, 0x0f,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x0a, 0x00,
      0x02, 0x02
   };

/**
 * WARNING une horreur
 */
uint8_t unBufferALaCon[4096] ={0};


/**
 * @brief Affichage d'un paquet
 */
void netDumpPacket(void * packet)
{
}

void virtioNetTraiterEmissions(VirtioReseau * vr)
{
   // OK, mais on les traite de quoi ?

   uint8_t             * buffers[2];
   int                   longueurs[2];
   VirtioFileVirtuelle * fv = &(vr->virtioPeripherique.filesVirtuelles[VR_FILE_EMISSION]);

   //printk_debug(DBG_KERNEL_NET, "emission (file %x)!!!\n", fv);

   // On ne veut plus être embêté
   //   virtioFileInterdireInterruption(fv);

   // On va chercher une trame, a priori dans une chaîne de buffers
   virtioFileRecupererBuffers(fv, (void*)buffers, longueurs, 2);

   // WARNING Horreur de debogage 
   /*printk("\n (E)Recu %d + %d :\n", longueurs[0], longueurs[1]);
   for (int i = 0; i < longueurs[1]; i++) {
     printk(" %x ", buffers[1][i]);
   }
   printk("\n");*/
   
   // On peut reprendre une activité normale
   //   virtioFileAutoriserInterruption(fv);
}

/**
 * Lorsque le périphérique nous prévient, on doit aller chercher une
 * trame (ou plusieurs) sur la file de réception.
 */
void virtioNetRecevoirTrame(VirtioReseau * vr)
{
   uint8_t             * buffers[2];
   int                   longueurs[2];
   int                   nbLu;
   VirtioFileVirtuelle * fv = &(vr->virtioPeripherique.filesVirtuelles[VR_FILE_RECEPTION]);

   /*
   printk_debug(DBG_KERNEL_NET, "reception (file %x)!!!\n", fv);

   printk_debug(DBG_KERNEL_NET, "File emission :\n");
   virtioAfficherFile(&(vr->virtioPeripherique.filesVirtuelles[VR_FILE_EMISSION]));
   
   printk_debug(DBG_KERNEL_NET, "File reception :\n");
   virtioAfficherFile(&(vr->virtioPeripherique.filesVirtuelles[VR_FILE_RECEPTION]));
   */
   
   // On ne veut plus être embêté
   //   virtioFileInterdireInterruption(fv);

   // On va chercher une trame, a priori dans une chaîne de buffers
   nbLu = virtioFileRecupererBuffers(fv, (void*)buffers, longueurs, 2);

   printk_debug(DBG_KERNEL_NET, "%d IT recues, trame : %d/%d+%d\n",
		vr->nbItRecues, nbLu, longueurs[0], longueurs[1]);

   /*
   if (nbLu) {
      // WARNING Horreur de debogage 
      printk("\n (R)Recu %d + %d :\n", longueurs[0], longueurs[1]);
      for (int i = 0; i < 42 ; i++) {
        printk(" 0x%x ", buffers[1][i]);
      }
      printk("\n");
   }
   */
   // On peut reprendre une activité normale
   //   virtioFileAutoriserInterruption(fv);
}

void virtioReseauPoll()
{
  virtioNetRecevoirTrame(&virtioReseau);
}

/**
 *  Cf [3] section 2.4.2
 */
void virtioNetGestionInt(void * pr)
{
   VirtioReseau * vr = (VirtioReseau *) pr;
   uint8_t isr;

   vr->nbItRecues++;
   
   printk_debug(DBG_KERNEL_NET, "Interruption %d !!!\n", vr->nbItRecues);

   // Est-ce moi qui suis visé ?
   inb((uint16_t)(vr->virtioPeripherique.pciEquipement->adresseES + VIRTIO_HIST_ISR), isr);
   if (isr & 0x1) {
      printk_debug(DBG_KERNEL_NET, "C'est pour moi, ...\n");
      //i8259aAckIRQ(vr->virtioPeripherique.pciEquipement->interruption); fait par le handler

      // La suite est à déférer dans une partie basse
      virtioNetRecevoirTrame(vr);
      //      virtioNetTraiterEmissions(vr); // WARNING : à vérifier si ça doit être là
   } else {
       printk_debug(DBG_KERNEL_NET, "Balek, ...\n");
   }
}

/**
 * @brief Initialisation d'un périphérique réseau virtio
 *
 * Séquence d'après [3] page 25 et section 2.2.1 (voir aussi [1]
 * section 3 mais en restant prudent !)
 */
int virtioNetInitPeripherique(int PCINumeroPeripherique)
{
   PCIEquipement       * pciEquip = PCIEquipementNumero(PCINumeroPeripherique);
   // WARNING, va le chercher dans le virtio
  
   VirtioFileVirtuelle * fr;
   uint8_t               addr;
   void                * pointeur; // Pour allouer de la mémoire en
				   // réception

   // On va construire un tableau de buffers (et un de leurs
   // longueurs) pour passer à virtioFournirBuffers
   void                * buffers[2];
   int                   longueurs[2];
   
   // On renseigne la structure
   virtioInitPeripheriquePCI(&(virtioReseau.virtioPeripherique),
			  PCINumeroPeripherique,
                            VIRTIO_NET_F_GUEST_CSUM  // C'est pas moi qui check
                          | VIRTIO_NET_F_GUEST_TSO4  // Je ne fais pas de TSO
			  | VIRTIO_NET_F_GUEST_TSO6
                          | VIRTIO_NET_F_GUEST_UFO   // Pas d'UFO svp
                          | VIRTIO_NET_F_MRG_RXBUF   // Je ne merge pas les buffers
                          | VIRTIO_NET_F_CTRL_VQ);   // Pas de canal de contrôle

   // On va tout de suite remplir la file de réception de
   // buffers ([3] page 26 point 5)
   fr = &(virtioReseau.virtioPeripherique.filesVirtuelles[0]);

   // ATTENTION ici je tente de passer des trames de taille max uniquement
   // d'où VIRTIO_TAILLE_TRAME_MAX qui remplace sizeof ...
   
   // Pas de malloc, ...
   pointeur = allouerPages(NB_PAGES(fr->taille*(VIRTIO_TAILLE_TRAME_MAX/*sizeof(VirtioReseauEntete)*/
						+ VIRTIO_TAILLE_TRAME_MAX)/2));

   // Concrètement, puisque le réseau préfixe systématiquement par un
   // entête à lui, on va lui fourni systématiquement une chaîne avec
   // un premier buffer pour l'entête, comme ça la trame sera toute
   // seule dans son buffer, donc directement manipulable ! Malin JP, ...
   for (int i = 0 ; i < fr->taille/2; i++) {
      buffers[0] = pointeur;
      longueurs[0] = sizeof(VirtioReseauEntete);
      pointeur += sizeof(VirtioReseauEntete);
      buffers[1] = pointeur;
      longueurs[1] = VIRTIO_TAILLE_TRAME_MAX;
      pointeur += VIRTIO_TAILLE_TRAME_MAX;
      virtioFournirBuffers(&(virtioReseau.virtioPeripherique),
			   VR_FILE_RECEPTION, // File réception
            	           buffers, longueurs,
                           2,
		           VRING_DESC_F_WRITE); // pour recevoir
   }
   
   // Lecture de l'adresse IEEE
   for (int i = 0; i < 6; i++){
      inb((uint16_t)(pciEquip->adresseES + 0x14 + i), addr);
      virtioReseau.adresseMAC[i] = addr;
   }

   // On définit notre fonction de gestion des interuptions
   if (i8259aAjouterHandler(pciEquip->interruption,
			virtioNetGestionInt,
			    &virtioReseau)){
      printk(PRINTK_CRITIQUE "Trop de handler sur l'interruption %d\n", pciEquip->interruption);
      paniqueNoyau("Pas possible");
      return ENOENT;
   }
   i8259aAutoriserIRQ(pciEquip->interruption);
   virtioReseau.nbItRecues = 0;
   
   return ESUCCES;
}

/**
 * Émission d'une trame via une interface ...
 */
void virtioNetEmettre(VirtioReseau * vr, uint8_t * trame)
{
   // On va construire un tableau de buffers (et un de leurs
   // longueurs) pour passer à virtioFournirBuffers
   void                * buffers[2];
   int                   longueurs[2];

   //   printk_debug(DBG_KERNEL_NET, "IN\n");

   // On ne délègue rien à l'interface
   virtioReseauEntete.flags = 0;
   virtioReseauEntete.typeGSO = 0;
   virtioReseauEntete.longueurEntete = 0;
   virtioReseauEntete.debutSommeControle = 0;
   virtioReseauEntete.decalageSommeControle = 0;

   buffers[0] = (void *)&virtioReseauEntete;
   longueurs[0] = sizeof(VirtioReseauEntete);
   buffers[1] = (void*)trame;
   longueurs[1] = 42;

   virtioFournirBuffers(&(virtioReseau.virtioPeripherique),
   	                1, // File émission
                        buffers, longueurs,
                        2,
		        0); // pour émettre

   //   printk_debug(DBG_KERNEL_NET, "OUT\n");
} 

/**
 * @brief Initialisation des périphériques
 */
int virtioNetInit()
{
   int PCINumeroPeripherique;
  
   printk_debug(DBG_KERNEL_NET, "IN\n");

   // On va chercher un peripherique virtio net
   PCINumeroPeripherique = PCIObtenirProchainEquipement(PCI_VENDEUR_VIRTIO,
							PCI_PERIPHERIQUE_VIRTIO_NET, -1);
   printk_debug(DBG_KERNEL_NET, "Peripherique PCI %d\n", PCINumeroPeripherique);

   // Initialisation de l'unique périphérique pour le moment
   if (virtioNetInitPeripherique(PCINumeroPeripherique)== 0) {
      printk_debug(DBG_KERNEL_NET, "Peripherique initialise !\n");
   }

   // Test d'émission
   virtioNetEmettre(&virtioReseau, requeteARP);

   printk_debug(DBG_KERNEL_NET, "out\n");
   return ESUCCES;
}

//Pour voir si je peux en faire 2 et avoir 2 IT
void virtioNetTestDeuxiemeEmission()
{
   printk_debug(DBG_KERNEL_NET, "in\n");
   virtioNetEmettre(&virtioReseau, requeteARP2);
   printk_debug(DBG_KERNEL_NET, "out\n");
}
