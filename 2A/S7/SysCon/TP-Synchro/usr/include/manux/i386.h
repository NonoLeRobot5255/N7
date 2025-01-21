/*----------------------------------------------------------------------------*/
/*      Définition des opérations spécifiques au processeur Intel.            */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#ifndef I386_DEF
#define I386_DEF

#include <manux/types.h>

void halt();
/*
 * Arret complet du système
 *
 * WARNING : codé dans interBasNiveau ... Est-ce là qu'il faut le coder et le
 * définir ?
 */

#define str(tr) \
   __asm__("str %0": "=g"(tr));


#define ltr(tr) \
   __asm__ __volatile__ ("ltr %%ax"::"a"(tr));

#define barriereMemoire() \
  __asm__("mfence");

/*
 * Description du processeur (d'après https://wiki.osdev.org/CPUID)
 */
static inline int descriptionProcesseur(int code, uint32_t description[3]) {
   uint32_t result;
   asm volatile("cpuid":"=a"(result),"=b"(*(description)),
               "=c"(*(description+2)),"=d"(*(description+1)):"a"(code));
   return (int)result;
}

/*
 * Calcul du numéro de la page contenant une adresse linéaire
 */
#define ADDR_VERS_PAGE(a) ((a)>>12)

/*
 * Chargement effectif de la GDT, implanté dans gestionGDT.nasm
 */
void _chargerGDT(uint32_t ad, uint16_t limite);

#endif
