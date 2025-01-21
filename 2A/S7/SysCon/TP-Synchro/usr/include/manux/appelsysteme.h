/*----------------------------------------------------------------------------*/
/*      Définition de la partie utilisateur des  appels système de ManuX.     */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#ifndef APPEL_SYSTEME_DEF
#define APPEL_SYSTEME_DEF

#include <manux/appelsystemenum.h>  /* Les numéros des AS définis */
#include <manux/types.h>

/*
 * Une macro permettant de définir l'interface d'un appel système
 * sans argument.
 */
#define appelSysteme0(numero, typeRetour, nom) \
  __attribute__ ((noinline))   typeRetour nom()                            \
   {                                           \
      typeRetour resultat;                     \
      __asm__ __volatile__ ("int %2"                         \
              : "=a"(resultat)                 \
              : "0" (numero),                  \
                "N" (MANUX_AS_INT));           \
      return resultat;                         \
   }

/*
 * Une macro permettant de définir l'interface d'un appel système
 * à un argument.
 */
#define appelSysteme1(numero, typeRetour, nom, typeArgument) \
  __attribute__ ((noinline))   typeRetour nom(typeArgument argument)                     \
   {                                                         \
      typeRetour resultat;                                   \
      __asm__ __volatile__ ("int %2"                         \
              : "=a"(resultat)                               \
              : "0" (numero),                                \
                "N" (MANUX_AS_INT));                         \
      return resultat;                                       \
   }

/*
 * Une macro permettant de définir l'interface d'un appel système
 * à deux arguments.
 */
#define appelSysteme2(numero, typeRetour, nom, typeArgument1, typeArgument2) \
  __attribute__ ((noinline))   typeRetour nom(typeArgument1 arg1, typeArgument2 arg2)                    \
   {                                                        \
      typeRetour resultat;                                  \
      __asm__ __volatile__ ("int %2"                        \
              : "=a"(resultat)                              \
              : "0" (numero),                               \
                "N" (MANUX_AS_INT));                        \
      return resultat;                                      \
   }

/*
 * Une macro permettant de définir l'interface d'un appel système
 * à trois arguments.
 */
#define appelSysteme3(numero, typeRetour, nom, typeArgument1, typeArgument2, typeArgument3) \
  __attribute__ ((noinline)) typeRetour nom(typeArgument1 arg1, typeArgument2 arg2, typeArgument3 arg3) \
   {                                                        \
      typeRetour resultat;                                  \
   __asm__ __volatile__ ("int %2"			    \
              : "=a"(resultat)                              \
              : "0" (numero),                               \
                "N" (MANUX_AS_INT));                        \
      return resultat;                                      \
   }

#endif
