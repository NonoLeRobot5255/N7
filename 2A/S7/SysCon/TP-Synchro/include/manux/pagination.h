/*----------------------------------------------------------------------------*/
/*      Définition des types et opérations spécifiques au mécanisme de        */
/*   pagination.                                                              */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#ifndef PAGINATION_DEF
#define PAGINATION_DEF

#include <manux/types.h>

/*
 * Type d'une entrée dans un répertoire de pages (PDE pour
 * "Page Directory Entry").
 */
typedef uint32_t PDE;

/*
 * Type d'une entrée dans un répertoire de tables (PTE pour
 * "Page Table Entry").
 */
typedef uint32_t PTE;

/*
 * Un répertoire de pages est simplement un tableau de PDE
 * (1024 max).
 */
typedef PDE * PageDirectory;

/*
 * Une table de pages est simplement un tableau de PTE
 * (1024 max).
 */
typedef PTE * PageTable;

/*
 * Répertoire de pagination global au système. Le but est d'avoir une
 * première configuration de la pagination, qui donne une vision "flat"
 * de la mémoire.
 */
extern PageDirectory repertoirePaginationSysteme;

void creerTablePaginationDirecte(PageDirectory * repertoirePagination,
                                 int tailleMemoireEtendue);
/*
 * Initialisation d'une table de pagination "directe", c'est à dire
 * qui conserve les adresses physiques dans l'espace virtuel.
 */

void creerTablePagination(PageDirectory * repertoirePagination);
/*
 * Initialisation d'une table de pagination pour une nouvelle tâche.
 * elle est créée dans la zone pointée par repertoirePagination et
 * englobe les pages réservées au système.
 */

int ajouterPage(PageDirectory * repertoirePagination,
                Page            adressePhysique,
                void          * adresseVirtuelle);
/*
 * Ajout d'une page dans l'espace d'adressage virtuel d'une
 * tâche à l'adresse voulue.
 */

int initialiserPagination(int tailleMemoireEtendue);
/*
 * Initialisation de la mémoire virtuelle
 */

#endif
