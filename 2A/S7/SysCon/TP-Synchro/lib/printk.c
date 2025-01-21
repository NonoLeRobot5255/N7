/**
 * @file printk.c
 * @bried Implantion des fonctions de base d'entrée-sortie.                     
 *                                                                            
 *                                                  (C) Manu Chaput 2000-2023 
 *                                                                            */
#include <manux/printk.h>

#ifdef MANUX_JOURNAL
#   include <manux/journal.h>
#else
#   include <manux/console.h>
#endif
#include <manux/appelsysteme.h>
#include <manux/memoire.h>       /* NULL */

#include <manux/debug.h>

#include <manux/arith64.h>
#include "../i386/arith64.c"   // WARNING, pourquoi dois-je faire ça ?

#define chiffre "0123456789abcdef"

/**
 * @brief : Écriture formattée dans une chaîne de caractères
 */
int sprintk(char * str, char * format, ...)
{
   va_list   argList;
   int       indice = 0;
   long long int       n;   // valeur associée à un %[l]d
   char      nombre[10];    // chaîne du nombre
   char    * s;             // valeur associée à un %s
   char      c;             // Affichage d'un caractère
   int       in;            // indice pour les boucles internes
   int       nbChiffres;    // pour les %[n]d
   int       base;          // de l'affichage entier
   int       prefixe;       // 0 int, 1 long int, 2 long long int
   
   va_start(argList, format);

   while (*format) {
      switch (*format) {
         case '%' :
            format++;
            // Lecture de la taille
            nbChiffres = 0;
            while ((*format <= '9') && (*format >= '0')) {
               nbChiffres = nbChiffres * 10 + *format - '0';
               format++;
	    }

	    // Pas forcément bien là, mais j'ai pas mieux dans l'immédiat
	    prefixe = 0;
	    if (*format == 'l') {
               format++;
	       if (*format == 'l') {
                  format++;
 		  prefixe = 2;
	       } else {
 		  prefixe = 1;
	       }
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
affent :          switch (prefixe) {
                     case 2 :
		        n = va_arg(argList, long long int);
		     break;
                     case 1 :
		        n = va_arg(argList, long int);
		     break;
                     default :
		        n = va_arg(argList, int);
                     break;
		  }
                  if (n < 0) {
		     n = -n;
		     str[indice++] = '-';
		  }
                  in = 0;
                  do {
                     nombre[in++] = chiffre[n%base];
                     n = n/base;
		  } while (n != 0);
                  while (nbChiffres > in) {
                     nbChiffres--;
                     str[indice++] = ' ';
		  }
                  do {
                     str[indice++] = nombre[--in];
                  } while (in);
               break; 
               case 's' :
                  s = va_arg(argList, char *);
                  in = 0;
                  while (s[in]) {
                     str[indice++] = s[in++];
		  }
               break;
               case 'c' :
                  c = va_arg(argList, char );
                  in = 0;
                  str[indice++] = c;
               break;
               default :
               break; 
	    }
         break;
	 default :
            str[indice++] = *format;
         break;
      }
      format++;
   }

   assert(indice < MAX_PRINTK_LENGTH);
   
   str[indice] = 0;

   va_end(argList);

   return indice;
}
	
void printk(char * format, ...)
{
   va_list   argList;
   char      chaine[MAX_PRINTK_LENGTH];   // WARNING, il faut une getion dynamique
                            // attention aux risques de telescopage avec la pile !
   int       indice = 0;
   long long int       n;   // valeur associée à un %[l]d
   char      nombre[10];    // chaîne du nombre
   char    * s;             // valeur associée à un %s
   char      c;             // Affichage d'un caractère
   int       in;            // indice pour les boucles internes
   int       nbChiffres;    // pour les %[n]d
   int       base;          // de l'affichage entier
   int       prefixe;       // 0 int, 1 long int, 2 long long int
   
   va_start(argList, format);

   while (*format) {
      switch (*format) {
         case '%' :
            format++;
            // Lecture de la taille
            nbChiffres = 0;
            while ((*format <= '9') && (*format >= '0')) {
               nbChiffres = nbChiffres * 10 + *format - '0';
               format++;
	    }

	    // Pas forcément bien là, mais j'ai pas mieux dans l'immédiat
	    prefixe = 0;
	    if (*format == 'l') {
               format++;
	       if (*format == 'l') {
                  format++;
 		  prefixe = 2;
	       } else {
 		  prefixe = 1;
	       }
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
affent :          switch (prefixe) {
                     case 2 :
		        n = va_arg(argList, long long int);
		     break;
                     case 1 :
		        n = va_arg(argList, long int);
		     break;
                     default :
		        n = va_arg(argList, int);
                     break;
		  }
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
               case 'c' :
                  c = va_arg(argList, char );
                  in = 0;
                  chaine[indice++] = c;
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

   assert(indice < MAX_PRINTK_LENGTH);
   
   chaine[indice] = 0;

   // On affiche 
#ifdef MANUX_JOURNAL
   journaliser(chaine);
#else
   consoleNoyauAfficher(chaine);
#endif
   
   va_end(argList);
}
