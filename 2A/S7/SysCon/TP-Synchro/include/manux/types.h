/*----------------------------------------------------------------------------*/
/*      Définition des types de base.                                         */
/*                                                                            */ 
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#ifndef MANUX_TYPES
#define MANUX_TYPES

#ifndef uint8_t
typedef unsigned char uint8_t;
#endif

#ifndef uint16
typedef unsigned short uint16_t;
#endif

#ifndef uint32_t
typedef unsigned long uint32_t;
#endif

#ifndef int32_t
typedef unsigned long int32_t;
#endif

#ifndef uint64_t
typedef unsigned long long uint64_t;
#endif

#ifndef size_t
typedef uint32_t size_t;
#endif

#ifndef booleen
typedef int booleen;
#endif

#ifndef TRUE
#   define TRUE 1
#endif

#ifndef FALSE
#   define FALSE 0
#endif

/*
 * Définition de la structure contenant tous les registres et sauvée lors d'un
 * pusha ([3] p 121). WARNING, ce n'est pas le meilleur endroit ...
 */
typedef struct _TousRegistres {
   uint32_t edi;
   uint32_t esi;
   uint32_t ebp;
   uint32_t esp;
   uint32_t ebx;
   uint32_t edx;
   uint32_t ecx;
   uint32_t eax;
} __attribute__((packed)) TousRegistres;

/*
 * Type des identificateurs de tâche
 */
typedef uint16_t TacheID;

/*
 * Une page mémoire est simplement vue comme une adresse.
 */
typedef void * Page;

/*
 * Un nombre de secondes écoulées
 */
typedef int32_t Temps;

/* 
 * Une structure permettant de décrire des dates/durées plus précisément
 */
typedef struct _ValTemps {
  Temps  secondes;
  uint32_t microSecondes;
} ValTemps;

#endif
