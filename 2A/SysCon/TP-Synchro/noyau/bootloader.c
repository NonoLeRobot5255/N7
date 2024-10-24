/**
 * @file bootloader.c
 * @brief Gestion de l'interfaçage avec le bootloader
 *
 *                                                  (C) Manu Chaput 2000-2023 
 */
#include <manux/bootloader.h>
#include <manux/debug.h>     // paniqueNoyau
#include <manux/string.h>    // memcpy

#define CMDLINE_MAX_LENGTH 512

static uint32_t magic; // Pour vérifier si on a été démarré par multiboot
InfoSysteme infoSysteme;
static char cmdLine[CMDLINE_MAX_LENGTH];

/**
 * @brief Lecture des informations fournies par le bootloader
 *
 * Cette fonction doit être la toute première invoquée car le passage
 * de paramètres se fonde en particulier sur le contenu de certains
 * registres.
 */
void bootloaderLireInfo() {
   InfoSysteme * _infoSysteme;
   
   // Multiboot laisse une signature : une valeur prédéfinie dans eax
   __asm__("movl %%eax,%0" : "=r"(magic));

   // Obtention du pointeur vers les informations fournies par l'outil
   // de chargement en mémoire
   __asm__("movl %%ebx,%0" : "=r"(_infoSysteme));

   // On se recopie le contenu dans une zone à nous
   memcpy(&infoSysteme, _infoSysteme, sizeof(InfoSysteme));
}

/**
 * @brief On prend le temps de construire les structures de données ici
 */
void bootloaderInitialiser()
{  
   // Un petit message
   printk_debug(DBG_KERNEL_BOOTLOADER, "Magic = 0x%x, is=0x%x (flags = 0x%x)\n",
	  magic,
	  infoSysteme,
	  infoSysteme.flags);

   // Quel est le bootloader ?
   switch (magic) {
      case MULTIBOOT_MAGIC :
         printk_debug(DBG_KERNEL_BOOTLOADER, "C'est multiboot qui nous a lance.\n");
      break;
      case MANUX_INIT_MAGIC :
         printk_debug(DBG_KERNEL_BOOTLOADER, "C'est init-manux qui nous a lance.\n");
      break;
      default :
         paniqueNoyau("Bootloader inconnue : 0x%x\n", magic);
   }

   // Alignement des modules à la page ? (Pas important pour nous)
   if ((infoSysteme.flags &  MULTIBOOT_PAGE_ALGIN) ==  MULTIBOOT_PAGE_ALGIN) {
      printk_debug(DBG_KERNEL_BOOTLOADER, "Alignement a la page\n");
   }

   // A-t-on des infos sur la mémoire ?
   if ((infoSysteme.flags & MULTIBOOT_MEMORY_INFO) == MULTIBOOT_MEMORY_INFO) {
      printk_debug(DBG_KERNEL_BOOTLOADER, "Base = %d, etendue = %d\n",
	  infoSysteme.memoireDeBase,
	  infoSysteme.memoireEtendue);
   } else {
      paniqueNoyau("Aucune information sur la memoire !\n");
   }

   // Informations de la ligne de commande (eg GRUB)
   if ((infoSysteme.flags & MULTIBOOT_INFO_CMDLINE) == MULTIBOOT_INFO_CMDLINE) {
      printk_debug(DBG_KERNEL_BOOTLOADER, "Command line : \"%s\"\n", infoSysteme.ligneCommande);
      int l = strlen(infoSysteme.ligneCommande);
      memcpy(cmdLine, infoSysteme.ligneCommande, ((l > 512)?512:l));
      cmdLine[(l > 512)?512:l] = 0;
      printk_debug(DBG_KERNEL_BOOTLOADER, "Command line : \"%s\"\n", infoSysteme.ligneCommande);
   }
}
