/**
 * @file multiconf/bootparam.h
 * @brief Exemple de configuration pour le passage de paramètres par le
 * bootloader.
 *
 *                                                     (C) Manu Chaput 2000-2023
 */

#ifdef MANUX_FICHIER_CONFIG
#   error "Cette chose ne devrait pas se produire !"
#   include MANUX_FICHIER_CONFIG
#else
#ifndef MANUX_CONFIG
#define MANUX_CONFIG

#define MANUX_FICHIER_MAIN main-bootparam

#include <config/base.h>
#include <config/console.h>
#include <config/printk.h>
#include <config/plan-memoire.h>
#include <config/gestion-memoire.h>

#include <config/verifications.h>

#endif  // MANUX_CONFIG
#endif  // MANUX_FICHIER_CONFIG
