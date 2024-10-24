/** 
 * @file : pci.c
 *
 * @brief : Fonctions de manipulation du bus PCI 
 * 
 * Liens utiles
 *   [1] https://wiki.osdev.org/PCI
 *   [2] https://en.wikipedia.org/wiki/PCI_configuration_space
 */
#include <manux/pci.h>
#include <manux/io.h>      // inl/outl/...
#include <manux/memoire.h> // NULL
#include <manux/debug.h>

/**
 * Le nombre maximal d'équipements sur un bus PCI
 */
#define PCI_NB_EQUIP_PAR_BUS 32

/**
 * @brief Les ports d'E/S de configuration du PCI
 */
#ifndef PCI_CONFIG_ADDRESS
#   define PCI_CONFIG_ADDRESS  0xCF8
#endif
#ifndef PCI_CONFIG_DATA
#   define PCI_CONFIG_DATA     0xCFC
#endif

/**
 * Les registres standards, voir en particulier [2] (Section Standardized registers)
 */
#define PCI_ID_VENDEUR    0x00
#define PCI_ID_EQUIPEMENT 0x02
#define PCI_REVISION      0x08
#define PCI_INTERRUPTION  0x3C
#define PCI_BAR_0         0x10   // Base Address Register
#define PCI_BAR_1         0x14
#define PCI_BAR_2         0x18
#define PCI_BAR_3         0x1C
#define PCI_BAR_4         0x20
#define PCI_BAR_5         0x24

/**
 * Pour identifier les BAR
 */
#define PCI_BAR_IO        0x01


#define PCI_AUCUN_VENDEUR 0xFFFF

/**
 * @brief : Une structure qui contient la description des équipements
 * PCI détectés
 */
int PCINombreEquipements = 0; // Le nombre d'équipements détectés

PCIEquipement PCIEquipements[MANUX_NB_MAX_EQUIPEMENTS_PCI];

/**
 * @brief : Lecture d'un mot sur le registre de config du PCI
 *
 * Les registres sont organisés comme décrits par exemple dans 
 * https://en.wikipedia.org/wiki/PCI_configuration_space#Standardized_registers
 *
 * On a donc un offset qui nous dit quel long aller chercher puis
 * éventuellement, via ses 2 bits de poids faible quel mot voire
 * quel octet. Ce denier "niveau d'adressage" est fait par un masque
 * (Et puisque les registres sont alignés sur 32 bits, on lit
 * systématiquement un long à l'offset privé de ces deux bits)
 */
uint32_t PCILireLong(uint8_t bus, uint8_t slot, uint8_t fonction, uint8_t offset)
{
   uint32_t result;
   uint32_t adresse = (((uint32_t)bus) << 16)
     | (((uint32_t)slot) << 11)
     | (((uint32_t)fonction) << 8)
     | (((uint32_t)offset) & 0xFC)
     | ((uint32_t)0x80000000);

   // On envoie l'adresse qui nous intéresse
   outl((uint16_t)PCI_CONFIG_ADDRESS, adresse);

   // On y lit un long conformément à [1]
   inl((uint16_t)PCI_CONFIG_DATA, result);

   return result;
}

uint16_t PCILireMot(uint8_t bus, uint8_t slot, uint8_t fonction, uint8_t offset)
{
   uint16_t result;

   // Si l'offset nous fait pointer sur le mot de poids fort, on décale
   // à gauche d'un mot (2 * 8). Sinon non (0 * 8). Puis on masque car
   // on ne veut qu'un mot
   result = (uint16_t)(PCILireLong(bus, slot, fonction, offset & ~0x3) >> ((offset & 2) * 8))& 0xFFFF;

   return result;
}

uint8_t PCILireOctet(uint8_t bus, uint8_t slot, uint8_t fonction, uint8_t offset)
{
   uint8_t result;

   // On décale de 0 à 3 octets en fonction des 3 bits de poids faible
   result = (uint8_t)(PCILireLong(bus, slot, fonction, offset & ~0x3) >> ((offset & 3) * 8))& 0xFF;

   return result;
}

/**
 * @brief : recherche des équipements PCI disponibles
 *
 * WARNING : On recherche les équipements sur un seul bus pour le moment.
 */
void PCIEnumerationDesEquipements()
{
   uint8_t  numEquipement;  // Pour boucler
   uint16_t idVendeur;
   uint16_t idEquipement;
   uint32_t adresse;        // Pour chercher les adresse d'E/S
   uint8_t  bar;            // Parcourir les BAR
   
   printk_debug(DBG_KERNEL_PCI, "Enumeration des equipements PCI ...\n");
   
   for (numEquipement = 0; numEquipement < PCI_NB_EQUIP_PAR_BUS; numEquipement++) {
      // Lecture des numéros de vendeur et d'équipement
      idVendeur = PCILireMot(0, numEquipement, 0, PCI_ID_VENDEUR);
      if (idVendeur != PCI_AUCUN_VENDEUR) {
         idEquipement = PCILireMot(0, numEquipement, 0, PCI_ID_EQUIPEMENT);

	 // Les identifiants
	 PCIEquipements[PCINombreEquipements].vendeur = idVendeur;
	 PCIEquipements[PCINombreEquipements].equipement = idEquipement;
	 
	 PCIEquipements[PCINombreEquipements].configAddress.nul = 0 ;
	 PCIEquipements[PCINombreEquipements].configAddress.registreOffset = 0 ;
	 PCIEquipements[PCINombreEquipements].configAddress.numeroFonction = 0 ;
	 PCIEquipements[PCINombreEquipements].configAddress.numeroEquipement = numEquipement ;
	 PCIEquipements[PCINombreEquipements].configAddress.numeroBus = 0 ;

	 // L'interruption
	 PCIEquipements[PCINombreEquipements].interruption =
	   PCILireOctet(0, numEquipement, 0, PCI_INTERRUPTION);

	 // On cherche l'adresse d'E/S
	 // On parcourt tous les registres mémoire
         for (bar = PCI_BAR_0; bar <= PCI_BAR_5; bar += 4) {
            adresse = PCILireLong(0, numEquipement, 0, bar);
	    // Est-ce une adresse d'E/S ?
	    if (adresse & PCI_BAR_IO) {
               // On est aligné sur 32 bits, les 2 bits de poids faible sont donc
	       // non signifiants
               PCIEquipements[PCINombreEquipements].adresseES = adresse & (~0x3);
	    } else {
               printk_debug(DBG_KERNEL_A_FAIRE, "Memory BARs a prendre en compte !\n");
	    }
	 }
	 
         printk_debug(DBG_KERNEL_PCI, "[%d] Vendeur/Id 0x%x/0x%x\n",
		      PCINombreEquipements, idVendeur, idEquipement);

	 PCINombreEquipements++;
	 if (PCINombreEquipements >= MANUX_NB_MAX_EQUIPEMENTS_PCI) {
            printk(PRINTK_CRITIQUE"Trop d'equipements PCI pour moi !\n");
            return;
	 }
      }
   }
   printk_debug(DBG_KERNEL_PCI, "%d equipements PCI\n", PCINombreEquipements);
}

/**
 *    WARNING remplacer les deux fonctions suivantes par une seule qui
 *    renvoie directement un pointeur.
 */ 


/**
 * @brief : récuperer l'identifiant du prochain équipement PCI
 * @param : precedent : indice du précédent (-1 pour chercher le premier)
 * @return : indice >= 0 si un équipement trouvé, -1 sinon
 */
int PCIObtenirProchainEquipement(uint16_t vendeur, uint16_t equipement, int precedent)
{
   int result = precedent;

   while ((++result < PCINombreEquipements)
	  && ((PCIEquipements[result].vendeur != vendeur)
	      || (PCIEquipements[result].equipement != equipement))
   ) {}

   if (result >= PCINombreEquipements)
      result = -1;
   
   return result;
}

/**
 * Obtention d'un pointeur vers une srtucture qui caractérise un
 * équipement PCI. Attention, aucune allocation/copie n'est faite, il
 * ne faut donc pas le modifier ni le détuire.
 */
PCIEquipement * PCIEquipementNumero(int n)
{
   if ((n >= 0) && (n < PCINombreEquipements))
      return &(PCIEquipements[n]);

   return NULL;
}
