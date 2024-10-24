/**
 * @file : sf/inoeud.c
 */
#include <manux/inoeud.h>
#include <manux/kmalloc.h>

/**
 * @brief : Création d'un INoeud
 */
INoeud * iNoeudCreer(void * prive, MethodesFichier * methodesFichier)
{
   INoeud * result = kmalloc(sizeof(INoeud));;

   if (result) {
      result->prive = prive;
      result->methodesFichier = methodesFichier;
   }
   
   return result;
}

