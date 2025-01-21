/**
 * @file bootloader.h
 * @brief Interfaçage avec les bootloader
 *                                                                          
 *                                                (C) Manu Chaput 2000 - 2023 
                                                                              */
#ifndef BOOTLOADER_CONFIG
#define BOOTLOADER_CONFIG

#include <manux/types.h>     // uint...

/**
 * @brief la signature d'un chargement par multiboot (legacy)
 */
#define MULTIBOOT_MAGIC 0x2BADB002

/**
 * @brief la signature d'un chargement par init-manux
 */
#ifndef MANUX_INIT_MAGIC
#   define MANUX_INIT_MAGIC 0x01c0ffee
#endif

/**
 * @brief les diverses informations que peut fournir le bootloader
 */
#define MULTIBOOT_PAGE_ALGIN   0x00000001
#define MULTIBOOT_MEMORY_INFO  0x00000002
#define MULTIBOOT_INFO_CMDLINE 0x00000004

/**
 * @brief Structure passée en paramètre par la phase d'init
 * (cf init-manux.nasm)
 */
typedef struct _InfoSysteme {
   uint32_t flags;           // Pour compatibilité avec multiboot
   uint32_t memoireDeBase;   // En Ko
   uint32_t memoireEtendue;  // En Ko
   uint32_t peripheriqueDemarrage ;
   char *   ligneCommande;
} InfoSysteme;

extern InfoSysteme infoSysteme;

/**
 * @brief Lecture des informations fournies par le bootloader
 *
 * Cette fonction doit être la toute première invoquée car le passage
 * de paramètres se fonde en particulier sur le contenu de certains
 * registres.
 */
void bootloaderLireInfo();

/**
 * @brief On prend le temps de construire les structures de données ici
 */
void bootloaderInitialiser();

#endif
 
