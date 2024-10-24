/**
 * @file kmalloc.h
 * @brief Définition de kmalloc
 */

#ifndef DEF_MALLOC
#define DEF_MALLOC

/**
 * On inclue la version choisie dans le fichier de configuration
 */
#if MANUX_KMALLOC == kmalloc-zs
#   include <manux/kmalloc-zs.h>
#else
#   error "Pas de malloc, ça craint !"
#endif

#endif // DEF_MALLOC
