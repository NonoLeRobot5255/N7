/*----------------------------------------------------------------------------*/
/*      Implantation des opérations de gestion des segments.                  */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#include <manux/errno.h>    // ENOMEM
#include <manux/debug.h>    // paniqueNoyau
#include <manux/i386.h>
#include <manux/segment.h>
#include <manux/printk.h>

DescriptorTable * gdtSysteme;

  struct __attribute__((__packed__)) {
      uint16_t taille;
      uint32_t adresse;
   } descripteurGDT;

int setDescripteurSegment(DescriptorTable * dt,
                          uint32_t adresse, uint32_t limite,
                          uint8_t type,
                          uint8_t gd0a)
/*
 * gd0a doit contenir dans son quadret de poids fort les bits G, D/B, 0
 * et AVL ([1] p 3-11)
 */
{
   if (dt->taille >= dt->capacite) {
      return -ENOMEM;
   }
   dt->descripteur[dt->taille].ds.limiteFaible = (uint16_t)((limite)&0xFFFF);
   dt->descripteur[dt->taille].ds.baseFaible = (uint16_t)((adresse)&0xFFFF); 
   dt->descripteur[dt->taille].ds.baseInter = (uint8_t)((adresse>>16)&0xFF);
   dt->descripteur[dt->taille].ds.type = type;
   dt->descripteur[dt->taille].ds.limiteFort = (uint8_t)((limite>>16)&0x0F)|gd0a;
   dt->descripteur[dt->taille].ds.baseFort = (uint8_t)((adresse>>24)&0xFF);

   return (dt->taille++)<<3;
}

int setDescripteurTSS(DescriptorTable * dt,
		      uint32_t adresse, uint32_t limite,
		      uint8_t type,
		      uint8_t g00a)
/*
 * g00a doit contenir dans son quadret de poids fort les bits G, 0, 0
 * et AVL ([1] p 6-7)
 */
{
   if (dt->taille >= dt->capacite) {
      return -1;
   }
   dt->descripteur[dt->taille].dt.limiteFaible = (uint16_t)((limite)&0xFFFF);
   dt->descripteur[dt->taille].dt.baseFaible = (uint16_t)((adresse)&0xFFFF); 
   dt->descripteur[dt->taille].dt.baseInter = (uint8_t)((adresse>>16)&0xFF);
   dt->descripteur[dt->taille].dt.type = type;
   dt->descripteur[dt->taille].dt.limiteFort = (uint8_t)((limite>>16)&0x0F)|g00a;
   dt->descripteur[dt->taille].dt.baseFort = (uint8_t)((adresse>>24)&0xFF);

   return (dt->taille++)<<3;
}

void inline chargerGDT(DescriptorTable * gdt)
/*
 * Chargement effectif de la GDT ; lgdt prend en paramètre l'adresse
 * d'une zone contenant la taille puis l'adresse de la GDT.
 * On va mettre en place ici un modèle "flat" (deux segments qui
 * couvrent 4G)
 */
{
#define USE_LEGACY_NO

#ifdef USE_LEGACY
   uint16_t limite = 8*gdt->taille - 1;
#else
   descripteurGDT.taille = 8*gdt->taille - 1;
   descripteurGDT.adresse = (uint32_t)&gdt->descripteur[0];
#endif
   
#ifdef USE_LEGACY
   /*   volatile uint8_t argument[6];
  
   argument[0] = (limite) & 0xFF;
   argument[1] = (limite>>8) & 0xFF;
   argument[2] = ((uint32_t)(&gdt->descripteur[0]) & 0xFF);
   argument[3] = (((uint32_t)(&gdt->descripteur[0])>>8) & 0xFF);
   argument[4] = (((uint32_t)(&gdt->descripteur[0])>>16) & 0xFF);
   argument[5] = (((uint32_t)(&gdt->descripteur[0])>>24) & 0xFF);
   */
  _chargerGDT((uint32_t)(&gdt->descripteur[0]), limite);

#else
   /*
   asm volatile (
      "movl %0, %%eax \n\t"
      "lgdt (%%eax) \n\t"
      "movl %%cr0, %%eax \n\t"
      "or $1, %%eax \n\t"
      "movl %%eax, %%cr0 \n\t"
      "movw $0x08, %%ax \n\t"
      "movw %%ax, %%cs \n\t"
      "movw $0x10, %%ax \n\t"
      "movw %%ax, %%ds \n\t"
      "movw %%ax, %%es \n\t"
      "movw %%ax, %%fs \n\t"
      "movw %%ax, %%gs \n\t"
      "movw $0x18, %%ax \n\t"
      "movw %%ax, %%ss \n\t"
      "ljmp $0x08,$vidageCache \n\t"
      "vidageCache : \n\t"
      ::"r"((uint32_t)&descripteurGDT):"eax"
   );

    */   
   asm volatile (
      "movl %0, %%eax \n\t"
      "lgdt (%%eax) \n\t"
      "ljmp $0x08,$vidageDuCache_%= \n\t"
      "vidageDuCache_%= : \n\t"
      "movw $0x10, %%ax \n\t"
      "movw %%ax, %%ds \n\t"
      "movw %%ax, %%es \n\t"
      "movw %%ax, %%fs \n\t"
      "movw %%ax, %%gs \n\t"
      "movw $0x18, %%ax \n\t"
      "movw %%ax, %%ss \n\t"
      "movl %%cr0, %%eax \n\t"
      "or $1, %%eax \n\t"
      "movl %%eax, %%cr0 \n\t"
      ::"r"((uint32_t)&descripteurGDT):"eax"
   );
#endif
}

void chargerLDT(DescriptorTable * ldt)
/*
 * Chargement effectif de la LDT ; lldt prend en paramètre l'adresse
 * d'une zone contenant la taille puis l'adresse de la LDT.
 */
{
   uint16_t limite = 8*ldt->taille - 1;
   volatile uint8_t argument[6];

   argument[0] = (limite) & 0xFF;
   argument[1] = (limite>>8) & 0xFF;
   argument[2] = ((uint32_t)(&ldt->descripteur[0]) & 0xFF);
   argument[3] = (((uint32_t)(&ldt->descripteur[0])>>8) & 0xFF);
   argument[4] = (((uint32_t)(&ldt->descripteur[0])>>16) & 0xFF);
   argument[5] = (((uint32_t)(&ldt->descripteur[0])>>24) & 0xFF);

   __asm__ __volatile__ ("lldt (%0)": :"a" ((char *)argument));// + sti ?
}

void initialiserGDT()
{
   int resultat;
#define MANUX_GDT_CS 0x08
#define MANUX_GDT_DS 0x10
#define MANUX_GDT_SS 0x18

   gdtSysteme = (DescriptorTable *) MANUX_ADRESSE_GDT;

   gdtSysteme->capacite = MANUX_GDT_NB_PAGES * MANUX_TAILLE_PAGE / sizeof(Descripteur);
   gdtSysteme->taille = 0;

   /* Le segment nul (obligatoire) */
   resultat = setDescripteurSegment(gdtSysteme, 0, 0, 0, 0);
   if (resultat != 0x00) {
      paniqueNoyau("Probleme sur le segment nul en %d\n", resultat);
   }

   // WARNING pour quoi si je change l'ordre de création (et donc bien
   // sur le numéro de façon cohérente) cela ne fonctionne pas !?
   //
   // Le segment de code qui commmence à l'adresse 0, avec une limite
   // à 1 méga(pages puisque Gr=1), donc 4G de mémoire.
   // g00a = 1100  (Gr=1 : blocs de 4K, Sz=1 32 bits protected)
   // type = 10011010
   //    present, priv=0, code/data, exec, dir up, read, access = 0
   resultat = setDescripteurSegment(gdtSysteme, 0, 0xFFFFFFFF, 0x9A, 0xC0);
   if (resultat != MANUX_GDT_CS) {
      paniqueNoyau("Probleme sur le segment de code en %d\n", resultat);
   }

   // Le segment de data qui commmence à l'adresse 0, avec une limite
   // à 1 méga(pages puisque Gr=1), donc 4G de mémoire.
   // g00a = 1100  (Gr=1 : blocs de 4K, Sz=1 32 bits protected)
   // type = 10010010
   //    present, priv=0, code/data, noexec, dir up, rw, access = 0
   resultat = setDescripteurSegment(gdtSysteme, 0, 0xFFFFFFFF, 0x92, 0xC0);
   if (resultat != MANUX_GDT_DS) {
      paniqueNoyau("Probleme sur le segment de donnees en %d\n", resultat);
   }

   // Le segment de pile qui commmence à l'adresse 0, avec une limite
   // à 1 méga(pages puisque Gr=1), donc 4G de mémoire.
   // g00a = 1100  (Gr=1 : blocs de 4K, Sz=1 32 bits protected)
   // type = 10010010
   //    present, priv=0, code/data, noexec, dir up, rw, access = 0
   resultat = setDescripteurSegment(gdtSysteme, 0, 0xFFFFFFFF, 0x92, 0xC0);
   if (resultat != MANUX_GDT_SS) {
      paniqueNoyau("Probleme sur le segment de pile en %d\n", resultat);
   }

   /* On charge la GDT */
   chargerGDT(gdtSysteme);
}

int ajouterDescTSS(DescriptorTable * dt,
		   void * adresse, uint32_t limite,
		   booleen busyTask)
{
   int resultat;

   if (busyTask) {
      resultat = setDescripteurTSS(dt, (uint32_t)adresse, limite, 0x8B, 0x90);
   } else {
      resultat = setDescripteurTSS(dt, (uint32_t)adresse, limite, 0x89, 0x90);
   }

   return resultat;
}

void busifier(uint16_t offsetTSS)
{
   gdtSysteme->descripteur[offsetTSS>>3].dt.type |= 0x02;
}

void debusifier(uint16_t offsetTSS)
{
   gdtSysteme->descripteur[offsetTSS>>3].dt.type &= 0xFD;
}
