/*----------------------------------------------------------------------------*/
/* Définition d'une interface de type fichiers. Elle pourra permettre un accès*/
/* homogène à différentes ressources (par exemple la console), et elle sera   */
/* évidemment nécessaire pour implanter un système de fichiers.               */
/*----------------------------------------------------------------------------*/
#define MANUX_FICHIER

/*
 * Le nombre maximal de fichiers manipulés par un processus
 * WARNING : sans aucun intéret pour le moment !
 */
#ifndef MANUX_NB_MAX_FICHIERS
#   define MANUX_NB_MAX_FICHIERS  4
#endif

/**
 * @brief Définition des noeuds d'information
 */
#define MANUX_INOEUDS

/** 
 * @brief : implantation des tubes
 */
#define MANUX_TUBES

/** 
 * @brief : l'implantation des tubes est-elle ré-entrante ?
 */
#define MANUX_TUBE_REENTRANT

/**
 * @brief : lorsqu'on crée une tâche, hérite-t-elle des fichiers ouverts ?
 */
#define MANUX_HERITER_FICHIERS

/*----------------------------------------------------------------------------*/
/* Définition de périphérique caractère. En pause, je n'en vois pas la        */
/* nécessité pour le moment                                                   */
/*----------------------------------------------------------------------------*/
//#define MANUX_PERIPHERIQUE_CARACTERE

