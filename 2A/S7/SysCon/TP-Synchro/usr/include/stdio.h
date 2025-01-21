/*----------------------------------------------------------------------------*/
/*      Définition des fonctions de base d'entrée-sortie du mode utilisateur. */
/*                                                                            */
/*                                                  (C) Manu Chaput 2002-2021 */
/*----------------------------------------------------------------------------*/
#ifndef _STDIO_H
#define _STDIO_H

#include <stdarg.h>

void printf(char * format, ...);
/*
 * Un grand classique ! Gérés pour le moment :
 *
 *    %[n]{dxo} %s \n
 */

int ecrireConsole(char * buffer, int nbBytes);

int lire(int fd, void * buffer, int nb);

int ecrire(int fd, void * buffer, int nb);

int fermer(int fd);

#endif
