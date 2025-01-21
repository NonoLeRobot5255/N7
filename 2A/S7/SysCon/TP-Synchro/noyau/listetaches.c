/*----------------------------------------------------------------------------*/
/*      Implantation des sous-programmes de gestion des listes de taches.     */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#include <manux/listetaches.h>
#include <manux/tache.h>
#include <manux/debug.h>         /* assert */
#include <manux/memoire.h>       /* NULL */

void initialiserListeTache(ListeTache * listeTache)
{
   listeTache->tete = NULL;
   listeTache->queue = NULL;
}

void insererCelluleTache(ListeTache   * listeTaches,
			 Tache        * tache,
                         CelluleTache * celluleTache)
{
   assert(listeTaches != NULL);
   assert(tache != NULL);
   assert(celluleTache != NULL);

   celluleTache->tache = tache;

   celluleTache->suivant = NULL;

   /* L'élément se retrouve aprés l'actuel dernier */
   if (listeTaches->queue != NULL) {
     listeTaches->queue->suivant = celluleTache;
   }

   /* L'élément inséré se retrouve à la fin */
   listeTaches->queue = celluleTache;

   /* Si la liste était vide, il se retrouve aussi en tête */
   if (listeTaches->tete == NULL) {
      listeTaches->tete = celluleTache;
   }

   assert(listeTaches->tete != NULL);
   assert(listeTaches->queue->tache == tache);
}

Tache * extraireTache(ListeTache * listeTaches)
{
   CelluleTache * celluleTache;

   celluleTache = listeTaches->tete;
  
   /* Si c'est la dernière */
   if (celluleTache == listeTaches->queue) {
      listeTaches->queue = NULL;
   }

   /* On sort la cellule de la liste et on la renvoie */
   if (celluleTache != NULL) {
      listeTaches->tete = celluleTache->suivant;
      return celluleTache->tache;
   }

   /* Si on est encore là, c'est que la liste est vide */
   return NULL;
}

