/*----------------------------------------------------------------------------*/
/*      Définition des opérations et types permettant de manipuler des listes */
/*   de tâches.                                                               */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef LISTETACHES_DEF
#define LISTETACHES_DEF

/*
 * Définition des listes de taches
 */
typedef struct _CelluleTache {
   struct _Tache        * tache;
   struct _CelluleTache * suivant;
} CelluleTache;

typedef struct _ListeTache {
   CelluleTache * tete;
   CelluleTache * queue;
} ListeTache;

void initialiserListeTache(ListeTache * listeTache);
/*
 * Initialisation d'une liste préalablement allouée
 */

void insererCelluleTache(ListeTache    * listeTaches,
                         struct _Tache * tache,
                         CelluleTache  * celluleTache);
/*
 * Insertion d'une Tache en fin de liste. Le troisième paramètre est
 * un pointeur sur une zone de type CelluleTache déjà allouée.
 */

struct _Tache * extraireTache(ListeTache * listeTaches);
/*
 * Extraction de la dernière tache de la liste. Attention, aucune
 * désallocation de la Cellule n'est faite.
 */

#endif
