/**
 * @file multiconf/printk.h
 * @brief Exemple de configuration pour l'utilisation du journal via l'interface
 * fichiers
 *
 *                                                     (C) Manu Chaput 2000-2023
 */

#ifdef MANUX_FICHIER_CONFIG
#   error "Cette chose ne devrait pas se produire !"
#   include MANUX_FICHIER_CONFIG
#else
#ifndef MANUX_CONFIG
#define MANUX_CONFIG

#define MANUX_FICHIER_MAIN main-virtio-journal

#include <config/base.h>
#include <config/bootloader.h>
#include <config/plan-memoire.h>
#include <config/gestion-memoire.h>
#include <config/console.h>
#include <config/printk.h>
#include <config/journal.h>
#include <config/systeme-fichiers.h>
#undef MANUX_TUBES
#include <config/pc-i386.h>
#include <config/intel-8259a.h>
#include <config/pci.h>
#include <config/virtio.h>

#include <config/verifications.h>

#endif  // MANUX_CONFIG
#endif  // MANUX_FICHIER_CONFIG
