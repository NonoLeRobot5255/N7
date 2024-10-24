/*----------------------------------------------------------------------------*/
/*      Outils permettant de générer un taille.conf pour la compilation de    */
/* ManuX                                                                      */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>
#include <error.h>

#define TAILLE_BLOC 512
  
int main(int argc,char * argv[])
{
   int nbBlocs ;              // Nombre de blocs du noyau
   int tailleBourage;         // Pour un nombre entier de blocs
   int premierSecteurRamDisk; // Nécessaire lors du chargement

   struct stat statNoyau, statInit;

   if (stat(argv[1], &statNoyau)) {
      perror("stat");
      return 1;
   }

   nbBlocs = ((int) statNoyau.st_size + TAILLE_BLOC)/TAILLE_BLOC;
   tailleBourage = nbBlocs * TAILLE_BLOC - (int) statNoyau.st_size;

   /*
   if (stat(argv[2], &statInit)) {
      perror("stat");
      return 1;
   }
   premierSecteurRamDisk = nbBlocs + ((int) statInit.st_size)/TAILLE_BLOC;
   */

   printf("# Fichier généré automatiquement, ne pas modifier\nMANUX_NB_SECT_KERNEL = %d\nMANUX_TAILLE_BOURRAGE = %d\n",
          nbBlocs,
          tailleBourage);

   return 0;
}
