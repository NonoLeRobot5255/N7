/**
 * @file : pci.h
 *                                                  (C) Manu Chaput 2021-2022
 */
#ifndef PCI_DEF
#define PCI_DEF

#include <manux/config.h>
#include <manux/types.h>

/**
 * @brief : structure permettant d'identifier un équipement PCI
 */
typedef struct _PCIEquipement {
   uint16_t vendeur;
   uint16_t equipement;

   uint8_t interruption;    // Le numéro d'IT utilisé par l'équipement   
   uint32_t adresseES;      // Pour dialoguer par E/S avec l'équipement
  
   struct _PCIConfigAddress {
      uint8_t nul:2;
      uint8_t registreOffset:6;
      uint8_t numeroFonction:3;
      uint8_t numeroEquipement:5;
      uint8_t numeroBus:8;
      uint8_t reserve:7;
      uint8_t active:1;
   } configAddress; // WARNING est-ce bien utile ?
} PCIEquipement;

/**
 * @brief : recherche des équipements PCI disponibles
 *
 * On recherche les équipements sur un seul bus pour le moment
 */
void PCIEnumerationDesEquipements();

/**
 * @brief : récuperer l'identifiant du prochain équipement PCI
 * @param : precedent : indice du précendent (-1 pour chercher le premier)
 * @return : indice >= 0 si un équipement trouvé, -1 sinon
 */
int PCIObtenirProchainEquipement(uint16_t vendeur, uint16_t equipement, int precedent);

/**
 * Obtention d'un pointeur vers une srtucture qui caractérise un
 * équipement PCI. Attention, aucune allocation/copie n'est faite, il
 * ne faut donc pas le modifier ni le détuire.
 */
PCIEquipement * PCIEquipementNumero(int n);

uint8_t PCILireOctet(uint8_t bus, uint8_t slot, uint8_t fonction, uint8_t offset);
uint16_t PCILireMot(uint8_t bus, uint8_t slot, uint8_t fonction, uint8_t offset);
uint32_t PCILireLong(uint8_t bus, uint8_t slot, uint8_t fonction, uint8_t offset);

#endif

