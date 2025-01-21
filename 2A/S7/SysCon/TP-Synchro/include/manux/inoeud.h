/**
 * @file : include/manux/inoeud.h
 * @brief : description des noeuds d'information
 *                                                     (C) Manu Chaput 2002-2023
 */
#ifndef INOEUD_DEF
#define INOEUD_DEF

#include <manux/types.h>

typedef struct _MethodesFichier MethodesFichier;

/**
 * @brief : Définition du type d'un périphérique
 * Pour le moment il sera représenté de façon assez classique par une
 * numérotation à deux champs : un majeur et un mineur.
 */
typedef struct _TypePeripherique {
   uint16_t majeur;
   uint16_t mineur;
} TypePeripherique;

/**
 * @brief : Un INoeud représente un fichier, d'un point de vue statique
 * Il s'agit donc de la description d'un fichier, même spécial, sur le disque.
 */
typedef struct _INoeud {
   TypePeripherique   typePeripherique;
   void             * prive;           // Données spécifiques à la nature
   MethodesFichier  * methodesFichier; // Les fonctions applicables à ce fichier
} INoeud;

/**
 * @brief : Création d'un INoeud
 */
INoeud * iNoeudCreer(void * prive, MethodesFichier  * methodesFichier);
  
#endif
