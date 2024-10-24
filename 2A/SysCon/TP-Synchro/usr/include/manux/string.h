/*----------------------------------------------------------------------------*/
/*      Définition des fonctions de manipulation des chaines.                 */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#ifndef DEF_MANUX_STRING
#define DEF_MANUX_STRING

#include <manux/types.h>

int strlen(const char * s);

void * memcpy(void *dest, const void *src, size_t n);

void * memset(void *dest, int val, size_t n);

  void bcopy (const void *src, void *dest, int n);
/*
 * Copie de n octets depuis src vers dest.
 */

#endif
