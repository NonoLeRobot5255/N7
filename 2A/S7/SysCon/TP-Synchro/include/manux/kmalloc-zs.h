/**
 * @file kmalloc-zs.h
 * @brief Une implatation simple de kmalloc fondé sur les zones
 * siamoises (buddy areas)
 *                                                   (C) Emmanuel Chaput 2023 */
#ifndef DEF_KMALLOC_ZS
#define DEF_KMALLOC_ZS

#include <manux/memoire.h>
#include <manux/types.h>

/**
 * @brief Initialisation du sytème kmalloc 
 */
void kmallocInitialisation();

#ifdef MANUX_KMALLOC_STAT
void kmallocAfficherStatistiques(char *prefixe);
#endif

/** 
 * @brief Allocation d'une zone de n octets
 * @return Pointeur sur la zone en cas de succès, NULL en cas d'échec 
 */
void * kmalloc(size_t n);

/**
 * @brief Libération d'une zone mémoire allouée
 */
void kfree(void * p);


#ifdef MANUX_KMALLOC_STAT
void kmallocAfficherStatistiques();
#endif // KMALLOC_STAT

#endif // DEF_KMALLOC_ZS
