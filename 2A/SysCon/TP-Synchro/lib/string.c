/*----------------------------------------------------------------------------*/
/*      Implantation des fonctions de manipulation des chaines.               */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/string.h>

/**
 * WARNING à refaire en assembleur
 */
void * memcpy(void *dest, const void *src, size_t n)
{
   char * d = dest;
   const char * s = src;
   while (n--)
      *d++ = *s++; 

   return dest;
}

/**
 * WARNING à refaire en assembleur
 */
void * memset(void *dest, int val, size_t n)
{
   char * d = dest;
   while (n--)
      *d++ = val; 

   return dest;
}


void bcopy (const void *src, void *dest, int n)
/*
 * bcopy/bzero ne sont ni ISO C ni POSIX (deprecated depuis 2001 et removed en 2008)
 */
{
   char * d = dest;
   const char * s = src;
   while (n--)
      *d++ = *s++; 
}

int strlen(const char * s)
{
   int result = 0;
   
   while (s[result]) {
      result++;
   }
   
   return result;
}
