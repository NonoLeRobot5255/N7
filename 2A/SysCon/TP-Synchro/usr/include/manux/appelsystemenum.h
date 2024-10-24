/*----------------------------------------------------------------------------*/
/*      Identification des appels système de ManuX.                           */
/*                                                                            */
/*      Il s'agit ici de définir les éléments communs à la partie noyau et la */
/* partie user.                                                               */
/*                                                  (C) Manu Chaput 2000-2023 */
/*----------------------------------------------------------------------------*/
#ifndef APPEL_SYSTEME_NUM_DEF
#define APPEL_SYSTEME_NUM_DEF

/*
 * Définition de l'interruption utilisée pour les appels système
 */
#ifndef MANUX_AS_INT
#   define MANUX_AS_INT 0x80
#endif

/*
 * Liste des appels système prédéfinis
 */
#define NBAS_IDENTIFIANT_TACHE 0
#define NBAS_ECRIRE_CONS       1
#ifdef MANUX_PAGINATION
#   define NBAS_OBTENIR_PAGES  2
#endif
#define NBAS_ECRIRE            3
#define NBAS_FORK              4
#define NBAS_CONSOLE           5
#define NBAS_BASCULER_TACHE    6
#define NBAS_CREER_TACHE       7
#define NBAS_DUMB              8
#define NBAS_LIRE              9
#ifdef MANUX_TUBES
#   define NBAS_TUBE          10
#endif
#define NBAS_FERMER           11

#endif // APPEL_SYSTEME_NUM_DEF
