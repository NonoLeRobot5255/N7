/**
 * @file journal.h
 * @brief Définition des outils de journalisation des messages du noyau.      
 * 
 *  Pour le moment, ces messages seront envoyés sur une console virtuelle. 
 *
 *                                                  (C) Manu Chaput 2002-2023
 */
#ifndef JOURNAL_DEF
#define JOURNAL_DEF

#include <manux/types.h>
#include <manux/fichier.h>
#include <manux/console.h>

/**
 * @brief Les différents niveaux d'affichage
 */
#define MANUX_JOURNAL_NIVEAU_PANIQUE      0
#define MANUX_JOURNAL_NIVEAU_URGENCE      1
#define MANUX_JOURNAL_NIVEAU_CRITIQUE     2
#define MANUX_JOURNAL_NIVEAU_ERREUR       3
#define MANUX_JOURNAL_NIVEAU_ATTENTION    4
#define MANUX_JOURNAL_NIVEAU_NOTIFICATION 5
#define MANUX_JOURNAL_NIVEAU_INFORMATION  6
#define MANUX_JOURNAL_NIVEAU_DEBUGAGE     7

/**
 * @brief Initialisation du système de journalisation.
 */
void journalInitialiser();
#ifdef MANUX_FICHIER
void journalInitialiserINoeud(INoeud * iNoeudConsole);
#endif

/**
 * @brief Affectation d'un fichier sur lequel seront envoyés les
 * messages journalisés
 */
void journalAffecterFichier(Fichier * pc);

/**
 * @brief Journalisation d'un message.
 */
void journaliser(char * message);

booleen journalOperationnel();


#endif
