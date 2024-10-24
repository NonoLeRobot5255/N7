/*----------------------------------------------------------------------------*/
/*      Implantation des opérations spécifiques au mécanisme de pagination.   */
/*                                                                            */
/*                                                       (C) Manu Chaput 2000 */
/*----------------------------------------------------------------------------*/
#include <manux/pagination.h>

#include <manux/config.h>     /* MANUX_TAILLE_PAGE */
#include <manux/memoire.h>

/*
 * Répertoire de pagination global au système. Le but est d'avoir une
 * première configuration de la pagination, qui donne une vision "flat"
 * de la mémoire.
 */
PageDirectory repertoirePaginationSysteme;

void creerTablePaginationDirecte(PageDirectory * repertoirePagination,
				 int tailleMemoireEtendue)
/*
 * Initialisation d'une table de pagination "directe", c'est-à-dire
 * qui conserve les adresses physiques dans l'espace virtuel.
 */
{
   int         nombrePages;
   int         i;             /* Pour compter les pages initialisées */
   Page      * pageCourante;  /* Pour parcourir les pages */
   PTE         PTECourante;   /* PDE de la page courante  */
   PDE         PDECourante;   /* PTE de la page courante  */
   int         indiceDirectory;     /* ... de la page courante  */
   int         indiceTable;         /* ... de la page courante  */
   PageTable   tableCourante;

   /* WARNING, valable pour la table système uniquement, et encore ... */
   * repertoirePagination = (PageDirectory) 0x60000;

   /* La première table est stoquée derrière le répertoire */
   /* Attention à l'arithmétique des pointeurs ! Pas de * sizeof(PDE) */
   tableCourante = *repertoirePagination; 

   /* WARNING, il faudrait peut-être passer l'adresse de fin */
   nombrePages = (tailleMemoireEtendue + 1024)/ 4;

   /* Construction des tables */
   pageCourante = (Page *)0;

   for (i = 1; i < nombrePages; i++) {

      /* Calcul des indices de la page courante */
      indiceTable = ((uint32_t)pageCourante >> 12) & 1023;
      indiceDirectory = ((uint32_t)pageCourante >> 22) & 1023;

      /* Construction d'une nouvelle PageTable */
      if (!indiceTable) {
         /* On met les tables les unes derrière les autres */
         /* Attention à l'arithmétique des pointeurs ! Pas de * sizeof(PDE) */
         tableCourante += 1024;
         PDECourante = ((uint32_t)tableCourante & 0xFFFFF000)
                       |0x003;
         (*repertoirePagination)[indiceDirectory] = PDECourante;
      }

      /* Calcul et enregistrement de la PTE */
      PTECourante = ((uint32_t)pageCourante & 0xFFFFF000)
                    |0x003;
      tableCourante[indiceTable] = PTECourante;

      /* On passe à la page suivante */
      /* Attention à l'arithmétique des pointeurs ! */
      pageCourante += MANUX_TAILLE_PAGE / sizeof(void *);
   }
}

void creerTablePagination(PageDirectory * repertoirePagination)
/*
 * Initialisation d'une table de pagination pour une nouvelle tâche.
 * elle est créée dans la zone pointée par repertoirePagination et
 * englobe le nombre de pages réservées au système (avec un mapping
 * direct).
 */
{
   int         numeroPage;      /* Pour compter les pages initialisées */
   Page      * pageCourante;    /* Pour parcourir les pages */
   PTE         PTECourante;     /* PDE de la page courante  */
   PDE         PDECourante;     /* PTE de la page courante  */
   int         indiceDirectory; /* ... de la page courante  */
   int         indiceTable;     /* ... de la page courante  */
   PageTable   tableCourante = 0;
   int         i;

   /* Le répertoire occupe une page */
   *repertoirePagination = allouerPage();

   /* On initialise le répertoire à zéro */
   for (i = 0; i < 1024; i++) {
     (*repertoirePagination)[i] = (PDE) 0;
   }

   /* Construction des tables */
   pageCourante = (Page)0;

   /* On insère les premières pages */
   for (numeroPage = 1;
        numeroPage < nombrePagesSysteme;
        numeroPage++) {
      /* Calcul des indices de la page courante */
      indiceTable = ((uint32_t)pageCourante >> 12) & 1023;
      indiceDirectory = ((uint32_t)pageCourante >> 22) & 1023;

      /* Construction d'une nouvelle PageTable */
      if (!indiceTable) {
         /* On alloue une nouvelle page */
         tableCourante = allouerPage();
         for (i = 0; i < 1024; i++) {
            tableCourante[i] = (PTE)0;
	 }
         PDECourante = ((uint32_t)tableCourante & 0xFFFFF000)
                       |0x003;
         (*repertoirePagination)[indiceDirectory] = PDECourante;
      }

      /* Calcul et enregistrement de la PTE */
      PTECourante = ((uint32_t)pageCourante & 0xFFFFF000)
                    |0x003;
      tableCourante[indiceTable] = PTECourante;

      /* On passe à la page suivante */
      /* Attention à l'arithmétique des pointeurs ! */
      pageCourante += MANUX_TAILLE_PAGE / sizeof(void *);
   }
}

int ajouterPage(PageDirectory * repertoirePagination,
                Page            adressePhysique,
                void          * adresseVirtuelle)
/*
 * Ajout d'une page dans l'espace d'adressage virtuel d'une
 * tâche à l'adresse voulue.
 */
{
   int       indiceDirectory; /* ... de la page */
   int       indiceTable;     /* ... de la page */
   PageTable tableCourante;

   /* Calcul des indices de la page courante */
   indiceTable = ((uint32_t)adresseVirtuelle >> 12) & 1023;
   indiceDirectory = ((uint32_t)adresseVirtuelle >> 22) & 1023;

   /* Création d'une nouvelle table si nécessaire */
   if ((*repertoirePagination)[indiceDirectory] == 0) {
      (*repertoirePagination)[indiceDirectory] =
                            (((uint32_t)allouerPage()) & 0xFFFFF000)
                            | 0x003;
   }

   /* Récupération de la table concernée */
   tableCourante = (PageTable)((*repertoirePagination)[indiceDirectory]
                               & 0xFFFFF000);

   /* Placement de l'adresse dans la table */
   tableCourante[indiceTable] = ((uint32_t)adressePhysique & 0xFFFFF000)
                    |0x003;

   return 0 ; 
}

int initialiserPagination(int tailleMemoireEtendue)
{
   /* Initialisation de la table système */
   creerTablePaginationDirecte(&repertoirePaginationSysteme,
			       tailleMemoireEtendue);

   /* Chargement en mémoire ... */
   __asm__ __volatile__ ("movl %0, %%cr3"
                         ::"a" ((char *)repertoirePaginationSysteme));

   /* ... puis validation du mode paginé */
   __asm__ __volatile__ ("movl %%cr0, %%eax\n\t"
                         "orl $0x80000000, %%eax\n\t"
                         "movl %%eax, %%cr0\n\t"::);
   return 0;
}

