/*----------------------------------------------------------------------------*/
/*      Implantation des sous-programmes de gestion des taches.               */
/*                                                                            */
/*                                                  (C) Manu Chaput 2000-2021 */
/*----------------------------------------------------------------------------*/
#include <manux/tache.h>
#include <manux/scheduler.h>  /* tacheEnCours */
#include <manux/memoire.h>
#include <manux/segment.h>
#ifdef MANUX_TACHE_CONSOLE
#   include <manux/console.h>
#endif
#include <manux/atomique.h>
#include <manux/segment.h>    /* setDescripteurSegment */
#include <manux/pagination.h> /* repertoirePaginationSysteme */

#include <manux/fichier.h>    /* pour créer stdout WARNING, à mettre ailleurs */
#include <manux/errno.h>      // Les codes d'erreur
#include <manux/string.h>     // memcpy
#include <manux/printk.h>
#include <manux/debug.h>

/**
 * @brief :Le numero de la prochaine tache
 * (WARNING : et si on cycle ?) 
 */
TacheID numeroProchaineTache = 1;

unsigned int nbActivations = 0; //  Nombre d'appels à activerTache

void basculerVersTache(Tache * tache)
/*
 * Activation d'une tâche
 */
{
   volatile uint32_t selecteur[2] = {0 , tache->indiceTSSDescriptor};

   __asm__ __volatile__ ("ljmp %0"::"m" (*selecteur));
}

/**
 * @brief la fonction principale d'exécution d'une tâche.
 *
 * C'est cette fonction qui va invoquer la fonction associée à la
 * tâche et qui devra nettoyer à la fin.
 */
void tacheExecuter()
{
#if defined(MANUX_TACHES) && !defined(MANUX_REENTRANT)
   // On commmence en mode noyau, ...
   entrerExclusionMutuelle(&verrouGeneralDuNoyau);
   assert(tacheDansLeNoyau == 0);
   tacheDansLeNoyau = tacheEnCours->numero;
#endif
   Tache * moi = tacheEnCours;
     
   printk_debug(DBG_KERNEL_TACHE, "Demarage de la tache %d (exec 0x%x) ...\n",
		moi->numero,
		moi->fonctionPrincipale);

#if defined(MANUX_TACHES) && !defined(MANUX_REENTRANT)
   // On commmence en mode noyau, ...
   tacheDansLeNoyau = 0;
   sortirExclusionMutuelle(&verrouGeneralDuNoyau);
#endif

   moi->fonctionPrincipale();

#if defined(MANUX_TACHES) && !defined(MANUX_REENTRANT)
      // On commmence en mode noyau, ...
      entrerExclusionMutuelle(&verrouGeneralDuNoyau);
      assert(tacheDansLeNoyau == 0);
      tacheDansLeNoyau = tacheEnCours->numero;
#endif

   printk_debug(DBG_KERNEL_TACHE, "Fin de la tache %d, ...\n", moi->numero);

   // On bascule dans les taches terminées
   moi->etat = Tache_Terminee;
   insererCelluleTache(&listeTachesTerminees,
                       moi,
                       (CelluleTache*)moi+sizeof(Tache));

   // On peut maintenant détruire les structures qui lui étaient
   // allouées

   // WARNING : à faire !

#if defined(MANUX_TACHES) && !defined(MANUX_REENTRANT)
   // On commmence en mode noyau, ...
   tacheDansLeNoyau = 0;
   sortirExclusionMutuelle(&verrouGeneralDuNoyau);
#endif

   // On rend la main
   ordonnanceur();
}

/**
 * @brief : Création d'une tâche. 
 *
 * Attention, elle n'est pas insérée dans la liste des tâches prêtes,
 * elle ne sera donc pas exécutée tant que ce ne sera pas fait.
 */
Tache * tacheCreer(CorpsTache corpsTache)
{
   void  * unePage;
   Tache * tache;
   void  * pile;      // Elle a sa propre pile

   printk_debug(DBG_KERNEL_TACHE, "(%d)in\n", numeroProchaineTache);

   /* On stoque les infos en zone système */
   unePage = allouerPage();
   if (unePage == NULL) {
      printk_debug(DBG_KERNEL_TACHE, "plus de memoire disponible\n");
      return NULL;
   }

   tache = (Tache *) unePage;

   pile = (void*) allouerPage();

   if (pile == NULL) {
      printk_debug(DBG_KERNEL_TACHE, "plus de memoire disponible\n");
      // WARNING : libérer la page de la tache
      return NULL;
   }
   
   /* Initialisation du descripteur de tache */
   tache->tss.Reserve1 = (uint16_t) 0;
   tache->tss.Reserve2 = (uint16_t) 0;
   tache->tss.Reserve3 = (uint16_t) 0;
   tache->tss.Reserve4 = (uint16_t) 0;
   tache->tss.Reserve5 = (uint16_t) 0;
   tache->tss.Reserve6 = (uint16_t) 0;
   tache->tss.Reserve7 = (uint16_t) 0;
   tache->tss.Reserve8 = (uint16_t) 0;
   tache->tss.Reserve9 = (uint16_t) 0;
   tache->tss.Reserve10 = (uint16_t) 0;
   tache->tss.Reserve11 = (uint16_t) 0;
   tache->tss.Reserve12 = (uint16_t) 0;
   tache->tss.CS = 0x08;  /* WARNING, hardcodé pas beau ! */
   tache->tss.DS = 0x10;  /* WARNING, hardcodé pas beau ! */
   tache->tss.ES = 0x10;  /* WARNING, hardcodé pas beau ! */
   tache->tss.FS = 0x10;  /* WARNING, hardcodé pas beau ! */
   tache->tss.GS = 0x10;  /* WARNING, hardcodé pas beau ! */
   tache->tss.SS = 0x18;  /* WARNING, hardcodé pas beau ! */
   tache->tss.ESP = (uint32_t)pile + 4092;  /* WARNING !! */
   if (corpsTache) {
      tache->fonctionPrincipale = corpsTache;
      tache->tss.EIP = (uint32_t)tacheExecuter;
   } else {
      tache->tss.EIP = NULL;
   }
   tache->tss.EFLAGS = (uint32_t)0x200;

   // Ajout de la tâche dans la GDT 
   tache->indiceTSSDescriptor = ajouterDescTSS(gdtSysteme,
					       &tache->tss,
					       0x67, FALSE);

   // On recharge la GDT (nécessaire suite changement de taille ?) 
   chargerGDT(gdtSysteme);

   // On lui affecte son numero
   tache->numero = numeroProchaineTache++;

#ifdef MANUX_FICHIER
   // Pas de fichier ouvert pour le moment
   for (int i = 0; i < MANUX_NB_MAX_FICHIERS; i++){
     tache->fichiers[i] = NULL;
   }
   tache->nbFichiersOuverts = 0;

#   ifdef MANUX_HERITER_FICHIERS
   if (tache->numero > 1) {
      // On hérite les fichiers de la tâche mère
      printk_debug(DBG_KERNEL_SYSFI, "Tache %d herite %d fichiers de tache %d\n",   
             tache->numero, tacheEnCours->nbFichiersOuverts, tacheEnCours->numero);
      for (int i = 0; i < MANUX_NB_MAX_FICHIERS; i++){
	 //tache->fichiers[i] = tacheEnCours->fichiers[i];
	 if (tacheEnCours->fichiers[i] != NULL) {
	    tache->fichiers[i] = fichierDupliquer(tacheEnCours->fichiers[i]);
	 }
      }
      tache->nbFichiersOuverts = tacheEnCours->nbFichiersOuverts;
      printk_debug(DBG_KERNEL_SYSFI, "Tache %d herite %d fichiers de tache %d OK\n",   
             tache->numero, tacheEnCours->nbFichiersOuverts, tacheEnCours->numero);
   }
#   endif
#endif
   
#ifdef MANUX_TACHE_CONSOLE   
   // Pas de console spécifique pour le moment
   tache->console = consoleNoyau();
#endif

#if defined(MANUX_APPEL_SYSTEME) && defined(MANUX_AS_AUDIT)
   for (int i = 0; i < NB_MAX_APPELS_SYSTEME; i++) {
     nbAppelsSystemeIn[i] = 0;
     nbAppelsSystemeOut[i] = 0;
   }
#endif
   // A priori elle est préemptible
   tache->nonPreemptible = 0;
   
   // Elle n'a pas encore été activée
   tache->nbActivations = 0;
   tache->tempsExecution = (Temps)0;
   
   // Zone mémoire utilisable 
   tache->tailleMemoire = (void *)(nombrePagesSysteme * MANUX_TAILLE_PAGE);

#ifdef MANUX_PAGINATION
   /* On lui affecte son PDBR */
   creerTablePagination((PageDirectory *)&(tache->tss.CR3));

   /* On ajoute la page décrivant la tâche en début de mémoire spécifique */
   ajouterPage((PageDirectory *)&tache->tss.CR3,
	       tache,
	       tache->tailleMemoire);
   tache->tailleMemoire += MANUX_TAILLE_PAGE;
#endif
   // printk("hhhhh\n");

   /* On lui affecte sa LDT */
   //   tache->ldt = (DescriptorTable *)(unePage + sizeof(Tache));
   /*   tache->ldt = (DescriptorTable *)allouerPage();
   tache->tss.LDT = (uint16_t)setDescripteurSegment(gdtSysteme,
					  (uint32_t)&(tache->ldt->taille),
					  LDT_NB_BYTES,
                                        0x82, 0xC0);
   */
   tache->ldt = NULL;
   tache->tss.LDT = NULL;
   
   /* On recharge la GDT */
   //   chargerGDT(gdtSysteme);

   /* Copie de la LDT, maintenant qu'elle est complète */
   //memcpy(tache->ldt, gdtSysteme, tailleGDTSysteme);


   /* Elle est prète à être exécutée */
   tache->etat = Tache_Prete;

   /* On affiche quelques infos */
   printk_debug(DBG_KERNEL_TACHE, "Tache[%d] = 0x%x\n", tache->numero, tache);
#ifdef MANUX_TACHE_CONSOLE
   printk_debug(DBG_KERNEL_TACHE, "cons = 0x%x, tss=0x%x, ldt=0x%x\n", tache->console, tache->tss, tache->ldt);
#else
   printk_debug(DBG_KERNEL_TACHE, "tss=0x%x, ldt=0x%x\n", tache->tss, tache->ldt);
#endif

   insererCelluleTache(&listeToutesLesTaches,
		       tache,
		       (CelluleTache*)tache+sizeof(Tache)+sizeof(CelluleTache));

   printk_debug(DBG_KERNEL_TACHE, "Tache %d creee, main = 0x%d ...\n",
		tache->numero,
		tache->fonctionPrincipale);

   printk_debug(DBG_KERNEL_TACHE, "out\n");
   return tache;
}

#ifdef MANUX_TACHE_CONSOLE   
/**
 * @brief Affectation d'une console à une tâche
 */
void tacheSetConsole(Tache * tache, struct _Console * cons)
{
   tache->console = cons;

#ifdef MANUX_FICHIER   // et sinon !?
   Fichier * f;
   INoeud * i;
   
   i = consoleCreerINoeud(cons);
   f = fichierCreer(i, O_WRONLY, 0);
   
   tache->fichiers[0] =  f;
#endif
}

#ifdef MANUX_FICHIER
/**
 * @brief Recherche du premier numéro de fichier ouvert disponible
 *
 * Attention : doit être protégé par un mutex !
 */
static int inline tacheNumFichierLibre(Tache * tache)
{
   int result = 0;

   while ((result < MANUX_NB_MAX_FICHIERS) && (tache->fichiers[result])) {
      result++;
   }
   return result;
}

/**
 * @brief Ajout de n fichiers dans la table des descripteurs de
 * fichier d'une tâche.
 *
 * On les affecte tous ou aucun. A priori, n = 1 la plupart du temps,
 * et éventuellement 2 pour les tubes, ...
 */
int tacheAjouterFichiers(Tache * tache, int n, Fichier * fichiers[], int * fds)
{
   int nbLibres;
   int result = 0;
   int fd;
   
   // WARNING à protéger par un mutex lock
   
   // A-t-on la place ?
   nbLibres = MANUX_NB_MAX_FICHIERS - tache->nbFichiersOuverts;
   
   // Si oui on affecte
   if (nbLibres >= n) {
      for (int i = 0; i < n; i++) {
         fd = tacheNumFichierLibre(tache);
	 assert(fd >= 0);
	 assert(fd < MANUX_NB_MAX_FICHIERS);
	 fds[i] = fd;
	 tache->fichiers[fd] = fichiers[i];
	 tache->nbFichiersOuverts ++;
	 result++;
      }
   }

   return result;
}
#endif

#endif
