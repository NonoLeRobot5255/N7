/*----------------------------------------------------------------------------*/
/*      Implantation des sous-programme de manipulation de la mémoire sous    */
/*   ManuX.                                                                   */
/*      On fait pour le moment un truc hyper minimaliste, sans aucune forme   */
/*   de vérification, le but étant juste de fournir un service élémentaire    */
/*   aux autres parties du noyau afin d'en avancer le développement.          */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#include <manux/config.h>
#include <manux/types.h>      /* TacheID */
#include <manux/debug.h>      /* assert */
#include <manux/memoire.h>
#include <manux/atomique.h>
#include <manux/pagination.h> /* ajouterPage() */
#include <manux/console.h>
#include <manux/i386.h>       // ADDR_VERS_PAGE

/**
 * @brief Obtention des adresses de base.
 * La récupération des variables du script du linker est un peu
 * ésotérique. Voir par exemple
 * https://stackoverflow.com/questions/48561217/how-to-get-value-of-variable-defined-in-ld-linker-script-from-c
 * pour un exemple, et surtout la doc pour une explication 
 * https://sourceware.org/binutils/docs/ld/Source-Code-Reference.html
 */
extern uint32_t _adresseDebutManuX[],
                _adresseFinManuX[],
                _adressePileManuX[],
                _adresseLimitePileManuX[];

uint32_t adresseDebutManuX = ((uint32_t)_adresseDebutManuX);
uint32_t adresseFinManuX = ((uint32_t)_adresseFinManuX);
uint32_t adressePileManuX = ((uint32_t)_adressePileManuX);
uint32_t adresseLimitePileManuX = ((uint32_t)_adresseLimitePileManuX);

/*
 * Début de la zone mémoire dans laquelle on mémorise l'occupation
 * des pages
 */
#ifndef MANUX_AFFECTATION_PAGES
#   define MANUX_AFFECTATION_PAGES 0x1000
#endif

/*
 * Nombre de pages communes à toutes les tâches.
 */
int nombrePagesSysteme = MANUX_NOMBRE_PAGES_SYSTEME;

/*
 * Le propriétaire de chaque page mémoire est identifié dans le
 * tableau suivant (0 <=> page libre). WARNING, pour le moment,
 * c'est 1 ou 0 (utilisé ou libre).
 */
TacheID * proprietairePage = (TacheID *)MANUX_AFFECTATION_PAGES ;

/*
 * Le nombre global de pages dans le système
 */
static int nombrePages = 0;
static int nombreDePagesAllouees = 0;

/*
 * Marquer une page comme réservée. WARNING : il faut se protéger par un mutex
 */
static void inline reserverPage(uint32_t i)
{
   if (proprietairePage[i] != (TacheID)0) {
      paniqueNoyau("Page %d deja prise\n", i);
   }
   nombreDePagesAllouees++;
   proprietairePage[i] = (TacheID)1;  // WARNING
}

/**
 * La libération qui va avec
 */
void libererPage(void * pageLiberee)
{
   int i = ((uint32_t) pageLiberee) / MANUX_TAILLE_PAGE;
   
   if (proprietairePage[i] == (TacheID)0) {
      paniqueNoyau("Liberation de la page %d non allouee !\n", i);
   }
   nombreDePagesAllouees--;
   proprietairePage[i] = (TacheID)0;
  
}

/*
 * Marquer une page comme libre (WARNING trouve un plus joli nom)
 */
static void inline demarquerPage(uint32_t i)
{
   proprietairePage[i] = (TacheID)0;
}

void initialiserMemoire(uint32_t tailleMemoireDeBase,
			uint32_t tailleMemoireEtendue)
{
   uint32_t i;                  // Pour compter les pages initialisées 
   uint32_t tailleProprietaire; // Taille nécessaire pour les gérer
   uint32_t nbrePagesManuX, nbrePagesPile;
   
   printk_debug(DBG_KERNEL_MEMOIRE, "base = %d, et = %d\n",
		tailleMemoireDeBase, tailleMemoireEtendue);

   printk_debug(DBG_KERNEL_MEMOIRE, "noyau d = 0x%x , f = 0x%x\n", adresseDebutManuX, adresseFinManuX);
   printk_debug(DBG_KERNEL_MEMOIRE, "pile  d = 0x%x , f = 0x%x\n", adressePileManuX, adresseLimitePileManuX);

   /* Les tailles sont données en Ko */
   nombrePages = (tailleMemoireDeBase + tailleMemoireEtendue) / 4;

   printk_debug(DBG_KERNEL_MEMOIRE, "%d pages de %d octets\n",
		nombrePages, MANUX_TAILLE_PAGE);

   /* De combien de pages a-t-on besoin pour les gérer ? */
   /* Pour le moment, la gestion d'une page demande 4 octets (bientôt 1 bit !) */
   tailleProprietaire = 4 * nombrePages  / MANUX_TAILLE_PAGE; 
   printk_debug(DBG_KERNEL_MEMOIRE, "tp %d\n", tailleProprietaire);
   
   /* Le tableau d'allocation des pages ne doit pas télescoper le noyau !*/
   assert((void*)(proprietairePage + tailleProprietaire*MANUX_TAILLE_PAGE)
	  < (void *)MANUX_KERNEL_START_ADDRESS);

   // Par défaut tout est libre
   for (i = 0; i < nombrePages; i++) {
      demarquerPage(i);      
   }

   // Les handlers : WARNING est-ce utile ?
   reserverPage(0);

   printk_debug(DBG_KERNEL_MEMOIRE, "Page  0x0         pour les gestionnaires\n");
   
   // La table d'allocation de la mémoire
   for (i=0 ; i < tailleProprietaire; i++){
     reserverPage(ADDR_VERS_PAGE(((uint32_t)proprietairePage))+i);
   }
   printk_debug(DBG_KERNEL_MEMOIRE, "Pages 0x%2x a 0x%2x pour la gestion memoire\n",
		ADDR_VERS_PAGE(((uint32_t)proprietairePage)),
		ADDR_VERS_PAGE(((uint32_t)proprietairePage)) + tailleProprietaire-1);
   
   // Le noyau
   nbrePagesManuX = (adresseFinManuX-adresseDebutManuX)/MANUX_TAILLE_PAGE
     + (((adresseFinManuX-adresseDebutManuX)%MANUX_TAILLE_PAGE)?1:0);
   for (i=0 ; i < nbrePagesManuX; i++) {
      reserverPage(ADDR_VERS_PAGE(adresseDebutManuX)+i);
   }
   printk_debug(DBG_KERNEL_MEMOIRE, "Pages 0x%x a 0x%x pour le noyau\n",
		ADDR_VERS_PAGE(adresseDebutManuX),
		ADDR_VERS_PAGE(adresseDebutManuX)+nbrePagesManuX-1);

   // La pipile
   nbrePagesPile = (adresseLimitePileManuX-adressePileManuX)/MANUX_TAILLE_PAGE
     + (((adresseLimitePileManuX-adressePileManuX)%MANUX_TAILLE_PAGE)?1:0);
   for (i=0 ; i < nbrePagesPile; i++) {
      reserverPage(ADDR_VERS_PAGE(adressePileManuX)+i);
   }
   printk_debug(DBG_KERNEL_MEMOIRE, "Pages 0x%x a 0x%x pour la pile\n",
		ADDR_VERS_PAGE(adressePileManuX),
		ADDR_VERS_PAGE(adresseLimitePileManuX)+nbrePagesPile-1);

   // La IDT
   for (i=0 ; i < MANUX_IDT_NB_PAGES; i++) {
      reserverPage(ADDR_VERS_PAGE(MANUX_ADRESSE_IDT)+i);
   }
   printk_debug(DBG_KERNEL_MEMOIRE, "Pages 0x%x a 0x%x pour la IDT\n",
		ADDR_VERS_PAGE(MANUX_ADRESSE_IDT),
		ADDR_VERS_PAGE(MANUX_ADRESSE_IDT) + MANUX_IDT_NB_PAGES-1);

   // La GDT
   for (i=0 ; i < MANUX_GDT_NB_PAGES; i++) {
      reserverPage(ADDR_VERS_PAGE(MANUX_ADRESSE_GDT)+i);
   }
   printk_debug(DBG_KERNEL_MEMOIRE, "Pages 0x%x a 0x%x pour la GDT\n",
		ADDR_VERS_PAGE(MANUX_ADRESSE_GDT),
		ADDR_VERS_PAGE(MANUX_ADRESSE_GDT) + MANUX_GDT_NB_PAGES-1);

   // Le BIOS (indéboulonable !)
   for (i=0 ; i < MANUX_BIOS_NB_PAGES; i++) {
      reserverPage(ADDR_VERS_PAGE(MANUX_ADRESSE_BIOS)+i);
   }
   printk_debug(DBG_KERNEL_MEMOIRE, "Pages 0x%x a 0x%x pour le BIOS\n",
		ADDR_VERS_PAGE(MANUX_ADRESSE_BIOS),
		ADDR_VERS_PAGE(MANUX_ADRESSE_BIOS)+MANUX_BIOS_NB_PAGES-1);

}

/*
void * reserverPageSysteme()
{
   void * pageAllouee = NULL;
   int    numeroPage;

   while (pageAllouee == NULL) {
      numeroPage = MANUX_DEBUT_MEMOIRE_ETENDUE/MANUX_TAILLE_PAGE;
      while (  (numeroPage < nombrePagesSysteme)
             &&(proprietairePage[numeroPage] != (TacheID) 0)) {
         numeroPage++;
      }
      // Si on trouve une page dispo 
      if (numeroPage < nombrePages) {
         // On essaie de la réserver 
         if (atomiqueTestInit((Atomique *)&(proprietairePage[numeroPage]),
                              1, 0)) {
            pageAllouee = (void *) (numeroPage * MANUX_TAILLE_PAGE);
	 }
      // Sinon inutile de continuer 
      } else {
         return NULL;
      }
   }
   //printk("return 0x%x\n", pageAllouee);
   return pageAllouee;
}
*/

void * allouerPage()
{
   void * pageAllouee = NULL;
   int    numeroPage = 0;

   // On cherche la première page libre
   while (  (numeroPage < nombrePages)
         &&(proprietairePage[numeroPage] != (TacheID) 0)) {
      numeroPage++;
   }

   /* Si on trouve une page dispo */
   if (numeroPage < nombrePages) {
      reserverPage(numeroPage);
      pageAllouee = (void *) (numeroPage * MANUX_TAILLE_PAGE);
   }

   printk_debug(DBG_KERNEL_MEMOIRE, "Page 0x%x allouee\n",
		numeroPage);

   return pageAllouee;
}

int nombrePagesAllouees()
{
  return nombreDePagesAllouees;
}

int nombrePagesTotal()
{
  return nombrePages;
}

/**
 * Combien de pages libes à partir de la page numeroPage incluse ?
 */
int nombrePagesLibres(unsigned int numeroPage)
{
   int result = 0;

   while ((proprietairePage[numeroPage+result] == (TacheID) 0)
	  && (numeroPage + ++result < nombrePages)) {
   }
   return result;
}

/** 
 * Allocation de plusieurs pages contigues
 */
void * allouerPages(unsigned int nombre)
{
   void * result = NULL;
   int    numeroPage = 0;

   // On cherche la première page libre
   while (  (numeroPage < nombrePages - nombre)
	    && (nombrePagesLibres(numeroPage) < nombre)) {
     // Inutile d'aller voir les suivantes, qui sont trop peu
     // nombreuses, ni celle d'après, qui est allouée.
     numeroPage += nombrePagesLibres(numeroPage) + 1;
   }

   /* Si on trouve une page dispo */
   if ((numeroPage < nombrePages)  && (nombrePagesLibres(numeroPage) >= nombre)){
     for (int i = numeroPage; i < numeroPage+nombre; i++) {
         reserverPage(i);
     }
     result = (void *) (numeroPage * MANUX_TAILLE_PAGE);
   }

   return result;
}

#if defined(MANUX_APPELS_SYSTEME) && defined(MANUX_PAGINATION)
int AS_obtenirPages(ParametreAS p, int nbPages)
{
   Page unePage;
   Tache * tache = tacheEnCours;

   /* Pour le moment, on ne sait faire qu'une à la fois */
   if (nbPages != 1) {
      return 0;
   }

   /* Obtention de la page */
   unePage = allouerPage();

   /* Ajout à la fin de la mémoire virtuelle de la tâche */
   ajouterPage((PageDirectory *)&tache->tss.CR3,
               unePage,
               tache->tailleMemoire);

   /* On note qu'on a davantage de mémoire */
   tache->tailleMemoire += MANUX_TAILLE_PAGE;

   return 1;
}
#endif
