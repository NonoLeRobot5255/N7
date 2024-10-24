/*----------------------------------------------------------------------------*/
/*      Définition des segments et leurs descripteurs et sélecteurs.          */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef SEGMENT_DEF
#define SEGMENT_DEF

#include <manux/types.h>

/*
 * Un descripteur de segment
 */
typedef struct _DescSegment {
   uint16_t limiteFaible;
   uint16_t baseFaible;
   uint8_t  baseInter;
   uint8_t  type;
   uint8_t  limiteFort;
   uint8_t  baseFort;
} DescSegment;

/*
 * Un descripteur de TSS ([1] p 6-7)
 */
typedef struct _DescTSS {
   uint16_t limiteFaible;
   uint16_t baseFaible;
   uint8_t  baseInter;  
   uint8_t  type;       /* P,DPL,010B1 */
   uint8_t  limiteFort; /* G,00,AVL,lim */
   uint8_t  baseFort;
} DescTSS;

typedef union _Descripteur {
   DescSegment ds;
   DescTSS     dt;
} Descripteur;

/*
 * La DescriptorTable est un tableau de descripteurs de segments auquel on ajoute
 * sa taille effective.
 */
typedef struct _DescriptorTable {
  int         capacite;
  int         taille;
  Descripteur descripteur[0];
} DescriptorTable;

#define tailleGDTSysteme (sizeof(int)+  \
                          sizeof(int)+  \
                          gdtSysteme->taille*sizeof(Descripteur))

extern DescriptorTable * gdtSysteme;

void initialiserGDT();
/*
 * Initiliser la GDT (Global Description Table)
 */

void chargerGDT(DescriptorTable * gdt);
/*
 * Chargement de la Global Descriptor Table
 */

void chargerLDT(DescriptorTable * ldt);
/*
 * Chargement de la Local Descriptor Table
 */

int ajouterDescTSS(DescriptorTable * dt,
		   void * adresse, uint32_t limite,
		   booleen busyTask);
/*
 * Ajout d'un descripteur de TSS à la DescriptorTable
 *
 * L'adresse et la limite du segment sont fournies en paramètre.
 * L'indice dans la DescriptorTable est fournie en retour (multiplié
 * par 8 comme l'index Intel).
 */

int setDescripteurSegment(DescriptorTable * dt,
                          uint32_t adresse, uint32_t limite,
                          uint8_t type,
                          uint8_t gd0a);
/*
 * Initialisation d'un  descripteur de segment dans une table de descripteur
 * gd0a doit contenir dans son quadret de poids fort les bits G, D/B, 0
 * et AVL ([1] p 3-11)
 */

#endif
