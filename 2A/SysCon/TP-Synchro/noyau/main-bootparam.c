/**
 * @file  : main-bootparam.c
 * @brief : Un exemple de noyau montrant le passage de paramètres au boot.
 *
 *                                                  (C) Manu Chaput 2000-2023 
 */
#include <manux/config.h>
#include <manux/console.h>
#include <manux/printk.h>
#include <manux/bootloader.h>

void startManuX()
{
   uint32_t magic; // Pour vérifier si on a été démarré par multiboot
   InfoSysteme * infoSysteme;

   // Multiboot laisse une signature : une valeur prédéfinie dans eax
   __asm__("movl %%eax,%0" : "=r"(magic));

   // Obtention du pointeur vers les informations fournies par l'outil
   // de chargement en mémoire
   __asm__("movl %%ebx,%0" : "=r"(infoSysteme));

   // Initialisation de la console noyau
   consoleInitialisation();

   // Un petit message
   printk("Magic = 0x%x, is=0x%x (flags = 0x%x)\n",
	  magic,
	  infoSysteme,
	  infoSysteme->flags);
   
   switch (magic) {
      case MULTIBOOT_MAGIC :
         printk("C'est multiboot qui nous a lance.\n");
      break;
      case MANUX_INIT_MAGIC :
         printk("C'est init-manux qui nous a lance.\n");
      break;
   }

   if ((infoSysteme->flags &  MULTIBOOT_PAGE_ALGIN) ==  MULTIBOOT_PAGE_ALGIN) {
     printk("Alignement a la page\n");
   }

   if ((infoSysteme->flags & MULTIBOOT_MEMORY_INFO) == MULTIBOOT_MEMORY_INFO) {
     printk("Base = %d, etendue = %d\n",
	  infoSysteme->memoireDeBase,
	  infoSysteme->memoireEtendue);

   }

   if ((infoSysteme->flags & MULTIBOOT_INFO_CMDLINE) == MULTIBOOT_INFO_CMDLINE) {
     printk("Command line : \"%s\"\n", infoSysteme->ligneCommande);
   }

   printk("That's all she wrote\n");

}   /* startManuX */


