/*----------------------------------------------------------------------------*/
/*      Définition des fichiers de Manux.                                     */
/*                                                                            */
/* Pour le moment très simplifié : on ne se soucis pas d'ouvrir ou de fermer  */
/* par exemple                                                                */
/*                                                  (C) Manu Chaput 2002-2023 */
/*----------------------------------------------------------------------------*/
#ifndef FICHIER_DEF
#define FICHIER_DEF

#include <manux/inoeud.h>
#include <manux/appelsysteme.h> // ParametreAS

typedef struct _Fichier Fichier;

/**
 * @brief Les différentes modes
 */
#define FMODE_READ   0x0001
#define FMODE_WRITE  0x0002

/**
 * @brief Les différents fanions
 *
 * A déplacer dans fcntl.h. Attention : non conformes à linux and co
 */
#define O_RDONLY     0x0001
#define O_WRONLY     0x0002
#define O_RDWR       (O_RDONLY|O_WRONLY)
#define O_NONBLOCK   0x0004
#define O_SYNC       0x0008

/**
 * @brief : Définition des opérations réalisables sur un fichier
 */
typedef struct _MethodesFichier {
   int (*ouvrir) (INoeud * iNoeud, Fichier * f, uint16_t fanions, uint16_t mode);
   int (*fermer) (Fichier * f);
   size_t (*ecrire) (Fichier * f, void * buffer, size_t nbOctets);
   size_t (*lire) (Fichier * f, void * buffer, size_t nbOctets);
} MethodesFichier;

/**
 * @brief : Qu'est-ce qu'un fichier ouvert du point de vue du noyau ?
 */
typedef struct _Fichier {
   void            * prive;   //!< Caractérisation du fichier ouvert
   INoeud          * iNoeud;  //!< Caractérisation de la structure
   uint16_t          mode;    //!< FMODE_READ, FMODE_WRITE, ... pour création
   uint16_t          fanions; //!< O_RDONLY, O_NONBLOCK, O_SYNC
  //   MethodesFichier * methodes;
} Fichier;

int fichierEcrire(Fichier * f, void * buffer, int nbOctets);

#ifdef MANUX_APPELS_SYSTEME

/**
 * @brief L'appel système permettant de fermer un fichier ouvert
 */
int sys_fermer(ParametreAS as, int fd);

int sys_ecrire(ParametreAS as, int fd, void * buffer, int nbOctets);
/**
 * L'appel système write
 */

int sys_lire(ParametreAS as, int fd, void * buffer, int nbOctets);
/**
 * L'appel système read
 */
#endif

void sfInitialiser();
/* 
 * Initialisation de tout ce qui est lié au SF
 */

/**
 * @brief : Ouverture d'un fichier. 
 * @param iNoeud : le noeud à ouvrir (in)
 * @param f : le fichier ouvert (out)
 *
 * On utilise la fonction d'ouverture du type de périphérique correspondant
 */
int fichierOuvrir(INoeud * iNoeud, Fichier * f, uint16_t fanions, uint16_t mode);

int fichierFermer(Fichier * f);

#ifdef MANUX_KMALLOC
/**
 * @brief Copie d'un fichier ouvert
 * 
 * Par exemple pour faire hériter un processus fils, ou pour un appel
 * de type dup 
 */
Fichier * fichierDupliquer(Fichier * f);

/**
 * @brief : création et ouverture d'un fichier
 */
Fichier * fichierCreer(INoeud * iNoeud, uint16_t fanions, uint16_t mode);

#endif // MANUX_KMALLOC

#endif
