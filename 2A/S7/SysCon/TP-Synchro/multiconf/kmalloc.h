/**
 * @file multiconf/kmalloc.h
 * @brief Exemple de configuration pour l'utilisation de kmalloc
 *
 *                                                     (C) Manu Chaput 2000-2023
 */

#ifdef MANUX_FICHIER_CONFIG
#   error "Cette chose ne devrait pas se produire !"
#   include MANUX_FICHIER_CONFIG
#else
#ifndef MANUX_CONFIG
#define MANUX_CONFIG

#define MANUX_FICHIER_MAIN main-kmalloc

#include <config/base.h>
#include <config/bootloader.h>
#include <config/plan-memoire.h>
#include <config/gestion-memoire.h>
#include <config/kmalloc.h>
#include <config/console.h>
#include <config/printk.h>
#include <config/stdlib.h>  // rand

#include <config/verifications.h>

#endif  // MANUX_CONFIG
#endif  // MANUX_FICHIER_CONFIG
