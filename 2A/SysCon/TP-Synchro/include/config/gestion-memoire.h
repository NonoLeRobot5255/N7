/*----------------------------------------------------------------------------*/
/*   Gestion de la mémoire. ATTENTION : à voir : peut-on décoréler ça de la   */
/* pagination ?                                                               */
/*----------------------------------------------------------------------------*/
/**
 * A-t-on des outils de base de gestion de la mémoire ? On ne parle
 * ici que d'une gestion par page.
 */
#define MANUX_GESTION_MEMOIRE

/*
 * Taille d'une page mémoire (4 Ko)
 */
#define MANUX_TAILLE_PAGE           0x1000

/*
 * Nombres de pages "système" c'est-à-dire communes à toutes les tâches.
 * WARNING, il serait bon de le calculer en fonction de la taille de la
 * mémoire physique. 
 */
#define MANUX_NOMBRE_PAGES_SYSTEME 0x800   /* 8 Mo */

/*
 * Adresse utilisée pour le tableau d'affectation des pages
 */
#ifndef MANUX_AFFECTATION_PAGES
#   define MANUX_AFFECTATION_PAGES 0x1000
#endif

/*
 * Active-t-on la pagination ?
 */
#define MANUX_PAGINATION

