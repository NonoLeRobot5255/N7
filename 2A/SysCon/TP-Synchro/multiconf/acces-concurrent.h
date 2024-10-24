/**
 * @file multiconf/acces-concurrent.h
 * @brief Exemple de configuration pour un test d'accès concurrents
 *
 *                                                     (C) Manu Chaput 2000-2023
 */

#ifdef MANUX_FICHIER_CONFIG
#   error "Cette chose ne devrait pas se produire !"
#   include MANUX_FICHIER_CONFIG
#else
#ifndef MANUX_CONFIG
#define MANUX_CONFIG

#define MANUX_FICHIER_MAIN main-acces-concurrent
#define MANUX_USR_INIT init-acces-concurrent.o

#include <config/base.h>
#include <config/plan-memoire.h>
#include <config/bootloader.h>       // Nécessaire pour construire mon bootloader
#include <config/systeme-fichiers.h>
#include <config/ramdisk.h>
#include <config/pc-i386.h>
#include <config/appels-systeme.h>  // pour le mode utilisateur
#include <config/consoles-virtuelles.h>
#include <config/printk.h>
#include <config/journal.h>
#include <config/noyau.h>
#include <config/taches.h>
#include <config/atomique.h>
#include <config/gestion-memoire.h>
#include <config/kmalloc.h>
#include <config/clavier.h>
#include <config/virtio.h>
#include <config/pci.h>
#include <config/stdlib.h>
#include <config/usr.h>

#include <config/verifications.h>

#endif  // MANUX_CONFIG
#endif  // MANUX_FICHIER_CONFIG
