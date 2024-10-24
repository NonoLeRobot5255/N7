/**
 * @file virtio.h
 *
 * WARNING : les fonctions fournirBuffers et recupererBuffers sont à
 * revoir. A priori en l'état, elles devraient fonctionner vu l'usage
 * que j'en fais. Mais je ne cherche pas à savoir quels descripteurs
 * de buffers sont libres, juste combien sont libres, et je les
 * utilise en round robin. On peut espérer qu'ils soient consommés et
 * rendu dans l'ordre dans lequel ils sont fournis, donc ça
 * passe. Mais il serait plus prudent de mettre en place une liste des
 * descripteurs libres (en plus c'est super simple).
 *
 * WARNING : je voudrais mettre toutes les définitions de types dans
 * le .c, mais le soucis c'est qu'elles doivent ensuite être utilisées
 * via des pointeurs (cf le premier champs de virtioReseauPeriph) et
 * comme pour le moment je n'ai pas de malloc, ...
 */
#ifndef VIRTIO_DEF
#define VIRTIO_DEF

#include <manux/pci.h>          // virtio est un système PCI
#include <manux/types.h>

/**
 * Toujours pour éviter de jouer avec des structures dynamiques, nous
 * allons limiter le nombre de files virtuelles de chaque équipement
 * de type virtio.
 * Tant qu'on ne fait que des périphériques réseau, on n'a besoin que
 * de deux files, ...
 */
#ifndef MANUX_VIRTIO_NB_MAX_FILES
#   define MANUX_VIRTIO_NB_MAX_FILES 3
#endif

/**
 * Les identifiants de vendeur et équipements
 */
#define PCI_VENDEUR_VIRTIO               0x1AF4
#define PCI_PERIPHERIQUE_VIRTIO_NET      0x1000
#define PCI_PERIPHERIQUE_VIRTIO_CONSOLE  0x1003

/**
 * Les bits d'état du pilote
 */
#define VIRTIO_RESET       0x00
#define VIRTIO_ACKNOWLEDGE 0x01
#define VIRTIO_DRIVER      0x02
#define VIRTIO_DRIVER_OK   0x04
#define VIRTIO_FEATURES_OK 0x08

/**
 * Les caractéristiques générales
 */
#define VIRTIO_F_RING_INDIRECT_DESC         0x10000000   // 28 
#define VIRTIO_F_RING_EVENT_IDX             0x20000000   // 29

/**
 * La position des champs principaux de configuration d'une interface
 * conforme à la spécification 0.9.5 [3] (dite "legacy" dans [1] mais
 * avec une organisation différente!)
 */
#define VIRTIO_HIST_CAPA_EQUIP     0x00  // Les capacités de l'équipement
#define VIRTIO_HIST_CAPA_PILOTE    0x04  // Les capacités du pilote
#define VIRTIO_HIST_ADDRESS_FILE   0x08  // Numéro de page de la file
					 // sélectionnée
#define VIRTIO_HIST_TAILLE_FILE    0x0C  // Taille de la file
#define VIRTIO_HIST_FILE_SEL       0x0E  // Sélection de la file 
#define VIRTIO_HIST_FILE_NOTIF     0x10  // Notification de la file
#define VIRTIO_HIST_ETAT           0x12  // Etat du périph et du pilote
#define VIRTIO_HIST_ISR            0x13

/**
 * Les flags de paramètrage des files
 */
#define VRING_DESC_F_NEXT  1
#define VRING_DESC_F_WRITE 2

/**
 * Description d'un buffer (voir par exemple struct vring_desc dans [1]
 * Section 2.4.4 ou dans [3] annexe A)
 * 
 */
typedef struct __attribute__((__packed__)) _VirtioDescripteurBuffer {
   uint64_t adresse;
   uint32_t longueur;
   uint16_t flags;
   uint16_t suivant;
} VirtioDescripteurBuffer;

/**
 * Description d'un buffer "disponible" ([3] Section 2.3.4)
 */
typedef struct __attribute__((__packed__)) _VirtioBufferDisponible {
   uint16_t flags;
   uint16_t indice;
   uint16_t indicesDesBuffer[];
   //uint16_t evenementUtilise; // On ne peut pas le déclarer !
} VirtioBufferDisponible;

/**
 * Description des éléments utilisés
 */
typedef struct __attribute__((__packed__)) _VirtioElementUtilise {
   uint32_t indiceBuffer; // Dans la table des descripteurs
   uint32_t longueur;     // Le nombre d'octets utilisés
} VirtioElementUtilise;

/**
 * Description d'un buffer "utilisé"
 */
typedef struct __attribute__((__packed__)) _VirtioBufferUtilise {
   uint16_t              flags;
   uint16_t              indice;
   VirtioElementUtilise  elementsUtilises[];
   //uint16_t            evenementDisponible; // On ne peut pas le déclarer
} VirtioBufferUtilise;

/**
 * Description d'une file virtuelle. Le format de cette structure
 * n'est pas imposé par virtio, car elle est utilisée uniquement dans
 * ce pilote.
 */
typedef struct __attribute__((__packed__)) _VirtioFileVirtuelle {
   uint16_t                  taille;
   uint16_t                  prochainDescripteur; // Le prochain à utiliser
   uint16_t                  nbDescripteursLibres;// A-t-on encore des desc ?
   VirtioDescripteurBuffer * tableDescripteurs;   // La table des
 					          // descripteurs de
                                                  // buffer
   VirtioBufferDisponible  * buffersDisponibles ;
   VirtioBufferUtilise     * buffersUtilises;
   uint16_t                  dernierIndiceUtilise; // WARNING le nom n'est pas bon je pense
} VirtioFileVirtuelle;

/**
 * Description d'un périphérique virtio
 */
typedef struct __attribute__((__packed__)) _VirtioPeripherique {
   PCIEquipement       * pciEquipement;  // Pointeur sur les caractéristiques PCI
   uint32_t              caracteristiques;
   VirtioFileVirtuelle   filesVirtuelles[MANUX_VIRTIO_NB_MAX_FILES];    
} VirtioPeripherique;

/**
 * Initialisation d'un périphérique de type virtio accédé en PCI.
 * L'essentiel de ce qui suit est conforme à la v0.9.5 a priori,
 * pas à la v1.0
 *
 * @param vp      pointeur sur une structure déjà allouée (ou statique)
 * @param PCINum  l'identifiant PCI
 * @param masque  les caractéristiques à *ne pas* utiliser
 */
int virtioInitPeripheriquePCI(VirtioPeripherique * vp,
                              int PCINum,
                              uint32_t masque);

/**
 * @brief : Fournir un buffer au périphérique.
 * @param vp   le périphérique virtio concerné
 * @param id   index de la file
 * @param bu   le buffer (pointeur sur les données/la place)
 * @param lg   la taille du buffer
 * @param fl   lecture/écriture (VRING_DESC_F_WRITE ou 0)
 * @return     le nombre de buffer effectivement fournis
 *
 * C'est effectivement le pointeur bu qui est fourni, donc l'appelant
 * ne doit pas le libérer !
 */
int  virtioFournirBuffer(VirtioPeripherique * vp,
			 uint16_t id,
			 void * bu, int lg,
			 uint16_t fl);


/**
 * @brief : Fournir un(e chaine de) buffer(s) au périphérique.
 *
 * @param fv   la file sur laquelle placer ce(s) buffer(s)
 * @param id   index de la file
 * @param bu   les buffers (tableau de pointeurs sur les données/la place)
 * @param lg   la taille des buffers
 * @param nb   le nombre de buffers
 * @param fl   lecture/écriture (VRING_DESC_F_WRITE ou 0)
 * @return     le nombre de buffers effectivement fournis
 *
 * C'est effectivement les pointeurs passés dans bu  qui sont fournis,
 * donc l'appelant ne doit pas les libérer !
 * S'il y a plusieurs buffers (nb > 1) c'est sous forme d'une chaîne
 * qu'ils sont fournis
 */
int virtioFournirBuffers(VirtioPeripherique * vp,
 			 uint16_t id,
			 void * bu[], int lg[], int nb,
			 uint16_t fl);

/** En travaux !! */
int virtioFileRecupererBuffers(VirtioFileVirtuelle * fv, void * bu[], int lg[], int nb);

/**
 * Affichage de l'état d'une file, à des fins de debug
 */
void virtioAfficherFile(VirtioFileVirtuelle * fv);

void virtioFileInterdireInterruption(VirtioFileVirtuelle * fv);
void virtioFileAutoriserInterruption(VirtioFileVirtuelle * fv);

#endif
