/**
 * @file sf/tube.c
 * @brief Une implantation des tubes de communication
 *
 * Un tube va être mis en oeuvre par un buffer mémoire dans lequel
 * seront écrites/lues les données.
 *
 * Attention, pour le moment, aucune distinction n'est faite entre les
 * extrémités du tube : ce qui est écrit (sur t[0] ou t[1]) est lu
 * (sur t[0] ou t[1]).
 */
#include <manux/tubes.h>
#include <manux/debug.h>
#include <manux/tache.h>     // tacheAjouterFichiers
#include <manux/scheduler.h> // tacheEnCours
#include <manux/fichier.h>
#include <manux/errno.h>    // ESUCCES
#include <manux/memoire.h>  // NULL
#include <manux/kmalloc.h>  // NULL
#include <manux/string.h>   // memcpy
#include <manux/atomique.h> // exclusions mutuelles
#include <manux/stdlib.h>   // bool type

MethodesFichier tubeMethodesFichier;

/**
 * @brief Capacité mémoire d'un tube, en nombre de pages
 */
#define MANUX_TUBE_NB_PAGES 1

#define MANUX_TUBE_CAPACITE (MANUX_TAILLE_PAGE * MANUX_TUBE_NB_PAGES)

#define MIN(a, b) (((a) < (b)) ? (a) : (b))

/**
 * @brief : Définition d'un tube
 */
typedef struct _tube
{
   uint8_t *donnees;   //< Pointeur sur la zone de données
   int taille;         //< Nombre d'octets présents dans le tube
   int indiceProchain; //< Position de la prochaine insertion

   int nbEcrivains;
   int nbLecteurs;
   ExclusionMutuelle verrou;
} Tube;

/**
 * @brief Ouverture d'un tube en tant que Fichier
 */
int tubeOuvrir(INoeud *iNoeud, Fichier *f, uint16_t fanions, uint16_t mode)
{
   Tube *tube = (Tube *)f->iNoeud->prive;
   exclusionMutuelleEntrer(&(tube->verrou));
   if (fanions & O_RDONLY)
   {
      tube->nbLecteurs++;
   }
   if (fanions & O_WRONLY)
   {
      tube->nbEcrivains++;
   }

   f->prive = NULL;
   exclusionMutuelleSortir(&(tube->verrou));
   return ESUCCES;
}

/**
 * @brief Fermeture d'un tube en tant que Fichier
 */
int tubeFermer(Fichier *f)
{

   printk_debug(DBG_KERNEL_TUBE, "in\n");
   Tube *tube = (Tube *)f->iNoeud->prive;
   exclusionMutuelleEntrer(&(tube->verrou));
   if (f->fanions & O_RDONLY)
   {
      tube->nbLecteurs--;
   }
   if (f->fanions & O_WRONLY)
   {
      tube->nbEcrivains--;
   }
   exclusionMutuelleSortir(&(tube->verrou));
   return ESUCCES;
}

booleen tubePlein(Tube *t)
{
   return t->taille == MANUX_TUBE_CAPACITE && t->nbLecteurs == 0;
}
/**
 * @brief Écriture dans un fichier
 */
size_t tubeEcrire(Fichier *f, void *buffer, size_t nbOctets)
{
   Tube *tube;
   int n = 0;
   int nbOctetsEcrits = 0; // Le nombre d'octets déja écrits
   printk_debug(DBG_KERNEL_TUBE, "in\n");

   // Peut-on décemment écrire dans le tube ?
   if ((f == NULL) || (f->iNoeud == NULL) || (f->iNoeud->prive == NULL))
   {
      return -EINVAL;
   }

   tube = f->iNoeud->prive;
   while (tubePlein(tube))
   {
   }
   printk("le tube est de taille %d\n", tube->taille);
   exclusionMutuelleEntrer(&(tube->verrou));

   // On fait une boucle, car il est possible que l'on doive écrire en
   // deux fois si on est proche de la fin du tableau qui contient les
   // données.
   do
   {

      // On n'écrit ni plus que ce qui est demandé, ni plus que ce
      // qu'on peut
      n = MIN(nbOctets - nbOctetsEcrits, MANUX_TUBE_CAPACITE - tube->taille);

      // On ne doit pas aller écrire au delà du buffer
      n = MIN(n, (MANUX_TUBE_CAPACITE - tube->indiceProchain));

      // On peut donc copier n octets dans le buffer à partir de la
      // position courante, sans risque de déborder
      memcpy(tube->donnees + tube->indiceProchain, buffer, n);

      tube->indiceProchain = (tube->indiceProchain + n) % MANUX_TUBE_CAPACITE;
      tube->taille += n;

      buffer += n;

      nbOctetsEcrits += n;
   } while (n > 0);

   printk_debug(DBG_KERNEL_TUBE, "out\n");
   exclusionMutuelleSortir(&(tube->verrou));
   return nbOctetsEcrits;
}

booleen tubeVide(Tube *t)
{
   return t->taille == 0 && t->nbEcrivains == 0;
}

size_t tubeLire(Fichier *f, void *buffer, size_t nbOctets)
{
   Tube *tube;
   int n = 0;
   int nbOctetsLus = 0;
   int indicePremier;

   printk_debug(DBG_KERNEL_TUBE, "in\n");

   // Peut-on décemment lire dans le tube ? (note : les deux premières
   // conditions sont assurées par l'appelant (fichierLire) a priori
   if ((f == NULL) || (f->iNoeud == NULL) || (f->iNoeud->prive == NULL))
   {
      return -EINVAL;
   }

   tube = f->iNoeud->prive;
   while (tubeVide(tube))
   {
   }

   printk("le tube est de taille %d\n", tube->taille);
   exclusionMutuelleEntrer(&(tube->verrou));

   do
   {
      // A partir de quel octet peut-on lire ?
      indicePremier = (tube->indiceProchain + MANUX_TUBE_CAPACITE - tube->taille) % MANUX_TUBE_CAPACITE;

      // On ne lit ni plus que ce qui est demandé, ni plus que ce
      // qu'on a
      n = MIN(nbOctets - nbOctetsLus, tube->taille);

      // On ne doit pas aller lire au delà du buffer
      n = MIN(n, (MANUX_TUBE_CAPACITE - indicePremier));

      printk_debug(DBG_KERNEL_TUBE, "Je vais lire %d\n", n);

      // On peut donc copier n octets dans le buffer à partir de la
      // position courante, sans risque de déborder
      memcpy(buffer, tube->donnees + indicePremier, n);

      indicePremier = (indicePremier + n) % MANUX_TUBE_CAPACITE;
      tube->taille -= n;

      buffer += n;

      nbOctetsLus += n;
   } while (n > 0);

   printk_debug(DBG_KERNEL_TUBE, "out\n");
   exclusionMutuelleSortir(&(tube->verrou));
   return nbOctetsLus;
}

/**
 * @brief Déclaration des méthodes permettant de traiter un tube
 * comme un fichier
 */
MethodesFichier tubeMethodesFichier = {
    .ouvrir = tubeOuvrir,
    .fermer = tubeFermer,
    .ecrire = tubeEcrire,
    .lire = tubeLire};

#ifdef MANUX_APPELS_SYSTEME
/**
 * @brief Implantation de l'appel système tube()
 *
 * On va créer un iNoeud décrivant le tube (une structure en mémoire)
 * puis deux descripteurs de fichiers, l'un pour écrire, l'autre pour
 * lire.
 */
int sys_tube(ParametreAS as, int *fds)
{
   INoeud *iNoeud;
   Fichier *fichiers[2];
   Tube *tube;

   printk_debug(DBG_KERNEL_TUBE, "Creation d'un tube (lire = 0x%x) ...\n", tubeLire);

   // Création de la structure
   tube = kmalloc(sizeof(Tube));
   if (tube == NULL)
   {
      return ENOMEM;
   }

   // Alocation de la mémoire tampon du tube
   if ((tube->donnees = allouerPage()) == NULL)
   {
      return ENOMEM;
   }

   // Initialisation des compteurs
   tube->taille = 0;
   tube->indiceProchain = 0;

   // Création de l'iNoeud qui décrit le tube dans le système
   iNoeud = iNoeudCreer(tube, &tubeMethodesFichier);

   // Création du fichier de sortie du tube (celui où on va lire)
   fichiers[0] = fichierCreer(iNoeud, O_RDONLY, 0);

   // Création du fichier d'entrée du tube (celui où on va écrire)
   fichiers[1] = fichierCreer(iNoeud, O_WRONLY, 0);

   // On ajoute les fichiers à la tâche
   if (tacheAjouterFichiers(tacheEnCours, 2, fichiers, fds) != 2)
   {
      return ENOMEM;
   }

   printk_debug(DBG_KERNEL_TUBE, "Tube cree entre %d et %d\n", fds[0], fds[1]);

   exclusionMutuelleInitialiser(&(tube->verrou));
   // Si on est encore là, c'est que tout s'est déroulé comme prévu !
   return ESUCCES;
}
#endif