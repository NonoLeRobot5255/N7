/*----------------------------------------------------------------------------*/
/*      Définition des opérations atomiques de ManuX.                         */
/*                                                                            */
/*      A faire : déplacer des choses dans plusieurs fichiers thématiques.    */
/*                                                  (C) Manu Chaput 2000-2023 */
/*----------------------------------------------------------------------------*/
#ifndef ATOMIQUE_DEF
#define ATOMIQUE_DEF

#include <manux/types.h>
#include <manux/tache.h>
#include <manux/listetaches.h>  /* Pour les listes de tâches en attente */
#include <manux/scheduler.h>    /* tacheEnCours */

/*
 * Type des données manipulées de façon atomique
 */
typedef uint32_t Atomique;

#define atomiqueInit(atom, val)\
   *(atom) = (val);

#define atomiqueLire(atom) \
   (atom)

static __inline__ uint32_t compareEtEchange(uint32_t * ptr, uint32_t cond, uint32_t val)
{
  /**
   Clobbers : "memory" car on va lire/écrire en mémoire, donc il faut
   une barrièe mémoire
   */
   uint32_t resultat;
   __asm__ volatile("cmpxchg %2, %1 \n\t"
		    : "=a"(resultat), "+m"(*ptr)
                    : "r"(val), "0"(cond)
		    : "memory");
   return resultat;
}

#define _compareEtEchange(ptr, cond, val)                \
  {					                 \
   uint32_t _cmpxchg_resultat;                           \
   __asm__ volatile("cmpxchg %2, %1 \n\t"                \
		    : "=a"(_cmpxchg_resultat), "+m"(ptr) \
                    : "r"(val), "0"(cond)                \
		    : "memory");                         \
   _cmpxchg_resultat;                                    \
}

static __inline__ booleen atomiqueTestInit(Atomique * atom, uint32_t val, uint32_t cond)
/*
 * La valeur de l'Atomique est comparée à la valeur cond ; en cas d'égalité,
 * l'Atomique prend la valeur val et le retour est 1. Sinon rien n'est fait
 * et le retour est 0.
 */
{
   uint8_t resultat;

   __asm__ ("cmpxchg %3, %2 \n\t"
            "sete %0 \n\t"
            : "=m"(resultat)
            : "a"(cond), "m"(*(volatile Atomique *)atom), "r"(val));
   return resultat;
}

/**
 * @brief Définition des exclusions mutuelles
 */
typedef struct _ExclusionMutuelle {
   Atomique   verrou;
   ListeTache tachesEnAttente;
#if defined(MANUX_ATOMIQUE_AUDIT)
   int        nbEntrees;
   int        nbSorties;
#endif
} ExclusionMutuelle;

/**
 * @brief Initialisation d'une exclusion mutuelle
 */
void exclusionMutuelleInitialiser(ExclusionMutuelle * em);

/**
 * @brief Entrée en exclusion mutuelle.
 * 
 * La tâche appelante est éventuellement mise en attente dans une
 * file spécifique. Elle n'en sera extraite que par la sortie d'une
 * tâche qui est dans la zone d'exclusion.
 */
void exclusionMutuelleEntrer(ExclusionMutuelle * em);

void exclusionMutuelleSortir(ExclusionMutuelle * em);

/**
 * @brief Empêcher la préemption pour la tâche en cours
 *
 * A utiliser de façon très limitée !
 */
#define tacheEnCoursInterdirePreemption()      \
   tacheEnCours->nonPreemptible++;

/**
 * @brief Autoriser la préemption pour la tâche en cours
 */
#define tacheEnCoursAutoriserPreemption()      \
   tacheEnCours->nonPreemptible--;

/**                                                                                                                        * @brief Définition des conditions
 */
typedef struct _condition {
   ListeTache tachesEnAttente;
#if defined(MANUX_ATOMIQUE_AUDIT)
   int nbSignaler;
   int nbDiffuser;
#endif
} Condition;

/**
 * @brief Initialisation d'une condition
 */
void conditionInitialiser(Condition * cond);

/**
 * @brief Attente de la prochaine occurence d'une condition
 *
 * La tâche appelante doit être dans l'exclusion mutuelle
 * (qui sera automatiquement libérée le temps de l'attente puis
 * reprise avant que cette fonction ne rende la main)
 */
void conditionAttendre(Condition * cond, ExclusionMutuelle * em);

/**
 * @brief Signaler une occurence d'une condition à une tâche en
 * attente 
 *
 * Attention, doit être utilisée sous la protection de l'exclusion
 * mutuelle détenue par les tâches en attente.
 * Ell est donc inutilisable dans un handler d'interruption.
 */
void conditionSignaler(Condition * cond);

/**
 * @brief Signaler une occurence d'une condition à toutes les tâches
 * en attente
 *
 * Attention, doit être utilisée sous la protection de l'exclusion
 * mutuelle détenue par les tâches en attente.
 * Ell est donc inutilisable dans un handler d'interruption.
 */
void conditionDiffuser(Condition * cond);
 
#if defined(MANUX_ATOMIQUE_AUDIT)
/**
 * @brief Affichage de l'état des variables d'exclusion mutuelle
 */

void exclusionsMutuellesAfficherEtat();

/**
 * @brief Affichage de l'état des variables condition
 */
void conditionsAfficherEtat();

#endif
#endif




/*
   Désassemblage d'une compilation sans optimisation de cette version

static __inline__ uint32_t compareEtEchange(uint32_t * ptr, uint32_t cond, uint32_t val)
{
   uint32_t resultat;
   __asm__ volatile("cmpxchg %2, %1 \n\t"
		    : "=a"(resultat), "+m"(ptr)
                    : "r"(val), "0"(cond)
		    : "memory");
   return resultat;
}

   État de la pile après la première instr :

10(%esp)   val
0c(%esp)   cond
08(%esp)   ptr
04(%esp)   @retour
00(%esp)   ebp

   0x00020044 <+0>:     push   %ebp             On sauve epb
   0x00020045 <+1>:     mov    %esp,%ebp        On l'utilise comme copie de esp
   0x00020047 <+3>:     sub    $0x4,%esp        esp qu'on aligne (ici à 2²)
   0x0002004a <+6>:     mov    0x10(%ebp),%edx  edx <- val
   0x0002004d <+9>:     mov    0xc(%ebp),%eax   eax <- cond
   0x00020050 <+12>:    cmpxchg %edx,0x8(%ebp)  cmpxchg %edx, ptr
   0x00020054 <+16>:    mov    %eax,-0x4(%ebp)  result <- %eax
   0x00020057 <+19>:    mov    -0x4(%ebp),%eax  Pas d'optimisation
   0x0002005a <+22>:    mov    %ebp,%esp        On remet %esp en place
   0x0002005c <+24>:    pop    %ebp             On restaure %ebp
   0x0002005d <+25>:    ret

 */

