/**
 * @file kmalloc-zs.c
 * @brief Allocation mémoire multi-usage pour des tailles jusqu'à 4092
 * octets
 *
 * La technique utilisée ici est celle des zones siamoises (buddy
 * system)
 */
#include <manux/debug.h>        // assert
#include <manux/memoire.h>
#include <manux/kmalloc-zs.h>

/**
 * @brief Un nombre qui nous permettra d'avoir un peu plus confiance
 * dans les blocs mémoire rendus par l'utilisateur.
 */
#define MANUX_KMALLOC_MAGIQUE 0x4832

/**
 * @brief Log2 de la taille max allouée
 */
#define MANUX_KMALLOC_ORDRE_MIN  3
#define MANUX_KMALLOC_ORDRE_MAX 12

/**
 * @brief Description d'un bloc mémoire fourni à l'utilisateur
 * En fait, on ne lui fourni que le pointeur vers la partie qu'il peut
 * utiliser.
 *
 * L'entête est une union car elle peut prendre deux formes. Lorsque
 * le bloc est alloué et fourni à l'utilisateur, on y stocque un
 * nombre "magique" qu'on espère retrouver, et une taille qui nous
 * permettra de savoir combien d'octets ont été alloués. Lorsque le
 * bloc est libre, on utilise cet entête pour mettre en place une
 * liste chaînée.
 */
typedef struct _enteteBlocMemoire {
   union {
      struct {
         uint16_t magique;
         uint16_t ordre;
      } alloue;      
      struct _enteteBlocMemoire * suivant;
   } e;
} enteteBlocMemoire;

/**
 * @brief Listes d'entêtes de blos libres
 */
enteteBlocMemoire * blocsLibres[MANUX_KMALLOC_ORDRE_MAX+1] = {NULL};

#ifdef MANUX_KMALLOC_STAT
int32_t nbPagesAllouees = 0;
uint32_t nbAlloc[MANUX_KMALLOC_ORDRE_MAX+1] = {0};
uint32_t nbFree[MANUX_KMALLOC_ORDRE_MAX+1] = {0};
#endif // MANUX_KMALLOC_STAT

void kmallocAfficherStatistiques(char *prefixe)
{
    uint16_t ordre;
    enteteBlocMemoire * bloc;
    int nb;

    printk("%s Pages allouees (kmalloc) / total : %d (%d) / %d\n",
	   prefixe,
	   nombrePagesAllouees(), nbPagesAllouees, nombrePagesTotal());
    printk("ordre alloc free  blocs\n");
    for (ordre = MANUX_KMALLOC_ORDRE_MIN ; ordre <= MANUX_KMALLOC_ORDRE_MAX; ordre++) {
       nb=0;
       for (bloc = blocsLibres[ordre]; bloc != NULL; bloc = bloc->e.suivant){
          nb++;
       }
       printk("   %2d  %4d  %4d  %4d\n", ordre, nbAlloc[ordre], nbFree[ordre], nb);
    }
}

/**
 * @brief Initialisation du sytème kmalloc 
 */
void kmallocInitialisation()
{
   // Pour le moment, on commence à vide !

   // Attention, on ne peut rien afficher car il faut que cette
   // fonction soit invoquée (le jour où elle fera quelque chose !)
   // avant l'initialisation de la console, au cas où la macro
   // MANUX_ATOMIQUE_AUDIT soit initialisée, ...
}

/**
 * @brief Calcul de l'ordre du bloc nécessaire
 */
static inline uint16_t ordreDe(uint16_t taille)
{
   uint16_t result = MANUX_KMALLOC_ORDRE_MAX;
   uint16_t tailleTotale = taille + sizeof(enteteBlocMemoire);

   assert(tailleTotale <= (1<<MANUX_KMALLOC_ORDRE_MAX));

   while (1<< (result - 1) >= tailleTotale) { 
      result --;
   }

   return result;
}

/**
 * @brief Découpe d'un bloc d'ordre o en deux blocs d'ordre o-1
 */
void decouperUnBloc(uint16_t o)
{
   enteteBlocMemoire * origine = blocsLibres[o];
   enteteBlocMemoire * part1, * part2;
   
   assert(blocsLibres[o] != NULL);

   // On supprime le bloc de la liste d'ordre o
   blocsLibres[o] = origine->e.suivant;

   // On descend d'un ordre
   o--;
   
   // Le suivant est à une distance d'un ordre inférieur
   part1 = origine;
   part2 = (enteteBlocMemoire *)((void *)origine + (1<<o));

   // On les insère en tête de liste
   part1->e.suivant = part2;
   part2->e.suivant = blocsLibres[o];
   blocsLibres[o] = part1;

}

/** 
 * @brief Allocation d'une zone de n octets
 * @return Pointeur sur la zone en cas de succès, NULL en cas d'échec 
 */
void * kmalloc(size_t n)
{
   enteteBlocMemoire * enteteBlocAlloue = NULL;
   uint16_t ordre;    //< Log2 de la taille totale
   uint16_t o;        //< indice de recherche de blocs
   
   ordre = ordreDe(n);
   if (ordre < MANUX_KMALLOC_ORDRE_MIN) {
      ordre = MANUX_KMALLOC_ORDRE_MIN;
   };
   
   assert(ordre <= MANUX_KMALLOC_ORDRE_MAX);
   assert(ordre >= MANUX_KMALLOC_ORDRE_MIN);
   
   // On recherche un bloc assez gros pour la demande
   o = ordre;
   while (( o <= MANUX_KMALLOC_ORDRE_MAX) && (blocsLibres[o] == NULL)) {
      o++;
   }

   assert(ordre <= MANUX_KMALLOC_ORDRE_MAX);
   assert(ordre >= MANUX_KMALLOC_ORDRE_MIN);

   // Si on a dépasser la taille max, c'est qu'on a rien trouvé. On
   // alloue alors un bloc de taille maximale.
   if (o > MANUX_KMALLOC_ORDRE_MAX) {
      // WARNING traiter cas où MANUX_KMALLOC_ORDRE_MAX est plus gros qu'une page ...
      blocsLibres[MANUX_KMALLOC_ORDRE_MAX] = allouerPage();
      if (blocsLibres[MANUX_KMALLOC_ORDRE_MAX] == NULL) {
         return NULL;
      } else {
#ifdef MANUX_KMALLOC_STAT
         nbPagesAllouees++;
#endif
         o = MANUX_KMALLOC_ORDRE_MAX;
	 blocsLibres[o]->e.suivant = NULL;
      }
   }
   
   // S'il est trop gros on le coupe en deux jusqu'à la bonne taille
   while (o > ordre) {
      decouperUnBloc(o);
      o--;
   }

   // On y est, par construction il y a un bloc de la bonne taille
   // on l'alloue
   enteteBlocAlloue = blocsLibres[o];
   blocsLibres[o] = enteteBlocAlloue->e.suivant;
   enteteBlocAlloue->e.alloue.magique = MANUX_KMALLOC_MAGIQUE;
   enteteBlocAlloue->e.alloue.ordre = ordre;
   
   if (enteteBlocAlloue == NULL) {
      return NULL;
   } else {
#ifdef MANUX_KMALLOC_STAT
      nbAlloc[ordre]++;
#endif

      return enteteBlocAlloue + 1;
   }
}

/**
 * @brief Réintégration d'un bloc dans le tableau des blocs libres, en
 * le fusionnant si possible avec son siamois.
 * @param bloc est le bloc mémoire à réintégrer, il est modifié en cas
 * de fusion (il pointe alors le résultat de la fusion et le siamois
 * est sorti des blocsLibres). Il n'est pas modifié si le bloc siamois
 * n'est pas libre. Dans tous les cas, il est réintégré.
 */
void reintegrerBloc(enteteBlocMemoire * bloc)
{
   uint16_t ordre = bloc->e.alloue.ordre; //< Ordre du bloc à intégrer
   enteteBlocMemoire * siamois, *prec = NULL;

   do {
      assert(ordre <= MANUX_KMALLOC_ORDRE_MAX);
      assert(ordre >= MANUX_KMALLOC_ORDRE_MIN);

      // On cherche le siamois, dont l'adresse ne diffère que par le
      // bit de l'ordre
      prec = NULL;
      siamois = blocsLibres[ordre];
      while ((siamois != NULL) && (((uint32_t)siamois ^ (1<<ordre)) != (uint32_t)bloc)) {
         prec = siamois;
	 siamois = siamois->e.suivant;
      }

      // Si le siamois était dans les libres, on l'enlève et  on procède
      // à la fusion
      if (siamois != NULL) {
         // On extrait le siamois
         if (prec == NULL){ // Si c'était le premier
            blocsLibres[ordre] = siamois->e.suivant;
         } else {           // Sinon
	    prec->e.suivant =  siamois->e.suivant;
         }
 
         // On recrée le bloc constitué de la fusion. L'adresse est celle
         // des deux avec le bit d'ordre ordre à zéro
         bloc = (enteteBlocMemoire *)(((uint32_t)bloc)&(~(1 << ordre)));

         // On remonte donc d'un ordre
         ordre++;
      }
   } while ((siamois != NULL) // Si la fusion a pu être faite, on
          &&(ordre < MANUX_KMALLOC_ORDRE_MAX)); // essaye de fusionner un ordre au dessus

   // A ce stade, on a effectué toutes les fusions possibles
   // concernant ce bloc. L'état final du bloc intègre ces
   // éventuellles fusions et l'ordre a donc été incrémenté à chaque
   // fusion. Il ne nous reste donc plus qu'à intègrer le bloc final
   // dans les libres 
   bloc->e.suivant = blocsLibres[ordre];
   blocsLibres[ordre] = bloc;      
   
}

/**
 * @brief Libération d'une zone mémoire allouée
 * Si le bloc avait été légitiment alloué, il est réintégré dans les
 * listes de blocs libres, si possible en le fusionnant avec son  bloc
 * siamois de sorte à reconstituer un plus gros bloc.
 */
void kfree(void * p)
{
   enteteBlocMemoire * bloc = (enteteBlocMemoire *)p ;

   bloc--;
 
   if (bloc->e.alloue.magique != MANUX_KMALLOC_MAGIQUE) {
     paniqueNoyau("Tentative de libérer un bloc 0x%x inconnu (m=0x%x, o=%d)\n",
		  p, bloc->e.alloue.magique, bloc->e.alloue.ordre);
   }

#ifdef MANUX_KMALLOC_STAT
   nbFree[bloc->e.alloue.ordre]++;
#endif

   if (bloc->e.alloue.ordre < MANUX_KMALLOC_ORDRE_MAX) {
      reintegrerBloc(bloc);
   }
}

