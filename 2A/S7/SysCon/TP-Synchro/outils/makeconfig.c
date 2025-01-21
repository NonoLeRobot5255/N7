/*----------------------------------------------------------------------------*/
/*      Outils permettant de générer un make.conf pour la compilation de      */
/* ManuX                                                                      */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>
#include <stdio.h>

#define addMacro(m)   \
   printf(#m " = 0x%x\n", m);
  
  
int main(int argc,char * argv[])
{
   printf("# Fichier généré automatiquement, ne pas modifier\n");

   addMacro(MANUX_TAILLE_PAGE);
   addMacro(MANUX_NOMBRE_PAGES_SYSTEME);
   addMacro(MANUX_KERNEL_START_ADDRESS);

   addMacro(MANUX_INIT_START_ADDRESS);
   addMacro(MANUX_STACK_SEG_16);

   addMacro(MANUX_ELF_HEADER_SIZE);
   addMacro(MANUX_ADRESSE_ECRAN);
   addMacro(MANUX_NB_SECT_INIT);
   addMacro(MANUX_NB_SECT_RAMDISK);
   addMacro(MANUX_SEGMENT_TRANSIT_RAMDISK);
   addMacro(MANUX_PREMIER_SECT_RAMDISK);

   addMacro(MANUX_portDonneesClavier);
   addMacro(MANUX_portCmdClavier);

   return 0;
}
