/*----------------------------------------------------------------------------*/
/*      Implantion des fonctions de base d'entrée-sortie du mode utilisateur. */
/*                                                                            */
/*                                                  (C) Manu Chaput 2002-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>     // Suivant la config on passe par fs ou pas
#include <manux/appelsysteme.h>
#include <stdio.h>

#define NULL ((void *)0)
#define chiffre "0123456789abcdef"

appelSysteme3(NBAS_ECRIRE, int, ecrire, int, void *, int);

appelSysteme3(NBAS_LIRE, int, lire, int, void *, int);

appelSysteme1(NBAS_FERMER, int, fermer, int);

/*
 * ecrireConsole est un appel système. Son "implantation" côté
 * utilisateur passe donc par une macro.
 */
appelSysteme2(NBAS_ECRIRE_CONS, int, ecrireConsole, char *, int);

/*
 * Un premier printf qui méritera bien des améliorations !
 */
void printf(char * format, ...)
{
   va_list   argList;
   char      chaine[128];  // WARNING, c'est nul
   int       indice = 0;
   int       n;             // valeur associée à un %d
   char      nombre[10];    // chaîne du nombre
   char    * s;             // valeur associée à un %s
   int       in;            // indice pour les boucles internes
   int       nbChiffres;    // pour les %[n]d
   int       base;          // de l'affichage entier

   //   printk("AA\n");
   va_start(argList, format);

   while (*format) {
      switch (*format) {
         case '%' :
            format++;
            /* Lecture de la taille */
            nbChiffres = 0;
            while ((*format <= '9') && (*format >= '0')) {
               nbChiffres = nbChiffres * 10 + *format - '0';
               format++;
	    }

            switch (*format) {
	       case 'o' :
                  base = 8;
                  goto affent;
	       case 'x' :
                  base = 16;
                  goto affent;
	       case 'd' :
                  base = 10;
affent :          n = va_arg(argList, int);
                  if (n < 0) {
		     n = -n;
		     chaine[indice++] = '-';
		  }
                  in = 0;
                  do {
                     nombre[in++] = chiffre[n%base];
                     n = n/base;
		  } while (n != 0);
                  while (nbChiffres > in) {
                     nbChiffres--;
                     chaine[indice++] = ' ';
		  }
                  do {
                     chaine[indice++] = nombre[--in];
                  } while (in);
               break; 
               case 's' :
                  s = va_arg(argList, char *);
                  in = 0;
                  while (s[in]) {
                     chaine[indice++] = s[in++];
		  }
               break;
               default :
               break; 
	    }
         break;
	 default :
            chaine[indice++] = *format;
         break;
      }
      format++;
   }

   chaine[indice] = 0;
   //   printk("BB\n");

#ifdef MANU_FS
   ecrire(1, chaine, indice); // WARNING : 1 à remplacer par stdout par exemple
#else
   // C'est exactement le but de l'AS ecrireConsole
   ecrireConsole(chaine, indice); 
#endif

   va_end(argList);
}
