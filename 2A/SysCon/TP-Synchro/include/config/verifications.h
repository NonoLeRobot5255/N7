/*----------------------------------------------------------------------------*/
/*   Et maintenant quelques vérifications de cohérence de la configuration.   */
/* Sans exhaustivité malheureusement.                                         */
/*----------------------------------------------------------------------------*/
/*
 * Pour la première, je ne suis pas si sûr, ...
 */
#ifdef MANUX_TACHES
#   ifndef MANUX_GESTION_MEMOIRE
#      error "MANUX_TACHES nécessite MANUX_GESTION_MEMOIRE !"
#   endif
#endif

#if defined(MANUX_CONSOLES_VIRTUELLES) && !defined(MANUX_CONSOLE)
#   error "MANUX_CONSOLES_VIRTUELLES nécessite MANUX_CONSOLE"
#endif

#if defined(MANUX_VIRTIO_CONSOLE) && !defined(MANUX_FICHIER)
#   error "MANUX_VIRTIO_CONSOLE nécessite MANUX_FICHIER"
#endif
/*
#if defined(MANUX_CLAVIER_CONSOLE) && !defined(MANUX_APPELS_SYSTEME)
#   error "MANUX_CLAVIER_CONSOLE nécessite MANUX_APPELS_SYSTEME"
#endif
*/

#if defined(MANUX_APPELS_SYSTEME) && !defined(MANUX_LIBI386)
#   error "MANUX_APPELS_SYSTEME nécessite MANUX_LIBI386 (pour les interruptions"
#endif

#if defined(MANUX_OUTILS_SYNCHRO) && !defined(MANUX_TACHES)
#   error "MANUX_OUTILS_SYNCHRO nécessite MANUX_TACHES"
#endif

#if defined(MANUX_VIRTIO_NET) && !defined(MANUX_RESEAU)
#   error "VIRTIO_NET est un périphérique nécessitant MANUX_RESEAU"
#endif

#if defined(MANUX_VIRTIO_NET) && !defined(MANUX_VIRTIO)
#   error "VIRTIO_NET est un périphérique nécessitant MANUX_VIRTIO"
#endif

#if defined(MANUX_VIRTIO) && !defined(MANUX_PCI)
#   error "VIRTIO est un système nécessitant MANUX_PCI"
#endif

#if defined(MANUX_PERIPHERIQUE_CARACTERE) && !defined(MANUX_FICHIER)
#   error "Les périphériques caractères nécessitent le type fichier"
#endif

#if defined(MANUX_CLAVIER_CONSOLE) && !defined(MANUX_CLAVIER)
#   error "MANUX_CLAVIER_CONSOLE nécessite MANUX_CLAVIER"
#endif

#if defined(MANUX_KMALLOC_STAT) && !defined(MANUX_KMALLOC)
#   error "MANUX_KMALLOC_STAT nécessite MANUX_KMALLOC"
#endif

#if defined(MANUX_TUBES) && !defined(MANUX_GESTION_MEMOIRE)
#   error "MANUX_TUBES nécessite MANUX_GESTION_MEMOIRE"
#endif

#if defined(MANUX_TUBES) && !defined(MANUX_KMALLOC)
#   error "MANUX_TUBES nécessite MANUX_KMALLOC"
#endif

#if defined(MANUX_ATOMIQUE_AUDIT) && !defined(MANUX_KMALLOC)
#   error "MANUX_ATOMIQUE_AUDIT nécessite MANUX_KMALLOC"
#endif
