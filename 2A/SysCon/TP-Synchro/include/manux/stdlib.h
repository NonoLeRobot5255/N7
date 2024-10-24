/**
 * @file stdlib.h
 * @brief Définition de quelques fonctions de base
 *                                                  (C) Manu Chaput 2020-2023 */
#ifndef MANUX_DEF_STDLIB
#define MANUX_DEF_STDLIB

#include <manux/types.h>

#define RAND_MAX 32767

/**
 * @brief Génération d'un nombre "aléatoire" entre 0 et RAND_MAX 
 */
uint32_t rand();

/**
 * @brief Modification de la graine du générateur "aléatoire"
 */
void srand(uint32_t graine);

#endif // MANUX_DEF_STDLIB
