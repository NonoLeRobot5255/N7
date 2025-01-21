/**
 * @file console.h
 * @brief Définition des fonctions de base d'accés à la console.     
 *                                                                          
 *      Une console est protégée par un verrou de type ExclusionMutuelle.    
 *   C'est à l'utilisateur de veiller à respecter les appels aux fonctions    
 *   d'entrée et de sortie de la section critique avant et aprés chaque       
 *   utilisation de la console. Bien sur le printf s'en occupe.               
 *      La seule fonction dans laquelle ces appels sont effectués est celle   
 *   permettant le basculement de console active.                             
 *                                                                            
 *                                                (C) Manu Chaput 2000 - 2023
                                                                               */

#ifndef MANUX_CONSOLE_DEF
#define MANUX_CONSOLE_DEF

#include <manux/config.h>
#include <manux/horloge.h>    // nbTopHorloge
#include <manux/types.h>
#include <manux/atomique.h>   // Accés unique à la console
#include <manux/ecran.h>

#ifdef MANUX_FICHIER
#   include <manux/fichier.h> // Une console est un fichier
#endif

/**
 * @brief Structure d'une console.
 *
 * Attention, en cas de consoles virtuelles,
 * on stoque ça au début d'une page qui contient également une copie
 * de l'écran. Il faut donc que la somme des deux tailles soit
 * inférieure à la taille d'une page. Ca nous laisse 96 octets pour
 * cette structure.
 */
typedef struct _Console {
   //! Adresse à laquelle se trouve le contenu affiché 
   char              * adresseEcran;
   //! Caractéristiques de l'écran
   uint8_t             nbLignes;
   uint8_t             nbColonnes;
   //! Position et attribut (couleur, ...) actuels
   int                 ligne, colonne ;
   unsigned char       attribut;

#ifdef MANUX_CONSOLES_VIRTUELLES
   //! Une copie pour lorsque la console est inactive
   char              * adresseEcranCopie;
  
   struct _Console   * suivante;    //!< Les consoles virtuelles sont chaînées
   struct _Console   * precedente;  //!< doublement chaînées
   int                 numero;      //!< Pour les identifier
#endif

#ifdef MANUX_CLAVIER_CONSOLE
   unsigned char     * bufferClavier;     // Pour les données du clavier
   uint16_t            nbCarAttente;
   uint16_t            indiceProchainCar; // Le prochain caractère à lire
#endif
  
} Console;

/**
 * @brief Initialisation du système de console sans notion de fichier
 * @return ESUCCES en cas de succès, autre chose sinon
 */
int consoleInitialisation();

#ifdef MANUX_FICHIER
/**
 * Les méthodes permettant de traiter une console comme un fichier
 */
extern MethodesFichier consoleMethodesFichier;

/**
 * @brief Initialisation du système de console 
 *
 * @param iNoeudConsole (out) un INoeud décrivant la console par défaut 
 * @return ESUCCES en cas de succès, autre chose sinon
 */
int consoleInitialisationINoeud(INoeud * iNoeudConsole);

/**
 * @brief : Création d'un iNoeud permettant de manipuler une console
 * @param : c (in) pointeur sur la console
 * @return : pointeur sur un INoeud
 */
INoeud * consoleCreerINoeud(Console * c);

#ifdef MANUX_KMALLOC
/**
 * @brief : Création d'un iNoeud permettant de manipuler une console
 * @param : c (in) pointeur sur la console
 * @return : pointeur sur un INoeud
 */
INoeud * consoleCreerINOeud(Console * c);
#   endif // MANUX_MALLOC
#endif // MANUX_FICHIER

/*
 * Choix des couleurs de texte et de fond (voir l'enum ci dessus)
 */
void consoleAffecterCouleurFond(Console * cons, Couleur coul);

void consoleAffecterCouleurTexte(Console * cons, Couleur coul);

/**
 * @brief Affichage d'un message sur une console
 *
 * Attention, aucun formatage n'est fait. En revanche, la chaine de
 * caractères doit être terminée par un zéro.
 */
void consoleAfficher(Console * cons, char * msg);

/**
 * @brief Affichage d'un message sur la console noyau
 */
void consoleNoyauAfficher(char * msg);

/*
 * Affichage d'un message à l'écran. Attention, aucun formatage
 * n'est fait. Seuls les nbOctets premiers octets sont affichés,
 * indépemment de la présence d'un caractère nul.
 */
void consoleAfficherN(Console * cons, char * msg, int nbOctets);

/*
 * Effacement (avec la couleur courante) et positionnement du curseur en
 * haut à gauche.
 */
void consoleEffacer(Console * cons);

/*
 * Affichage d'un entier sur la console
 */
void consoleAfficherEntier(Console * cons, int n);

/*
 * Affichage d'un entier sur la console. En hexa sur le nbre d'octets
 * voulu.
 */
void consoleAfficherRegistre(Console * cons, int nbOctets, int reg);

/**
 * @brief Obtention d'un pointeur sur la console par défaut
 */
Console * consoleNoyau();

#ifdef MANUX_CLAVIER_CONSOLE
/**
 * @brief Lecture d'octets depuis une console
 */
int consoleLire(Console * cons, void * buffer, int nbOctets);
#endif

/*
 * La notion de console virtuelle permet de gérer plusieurs affichages
 * disjoints. Chaque console est donc gérée indépendemment des autres.
 * Une seule est affichée à l'écran à un instant t.
 * Les consoles sont stoquées dans un tableau et repérées par leur
 * indice dans ce tableau.
 */
#ifdef MANUX_CONSOLES_VIRTUELLES

/**
 * @brief : Création (avec allocation mémoire) d'une console
 */
Console * creerConsoleVirtuelle();

/*
 * Pointeur vers la console active
 */
extern Console * consoleActive;

/*
 * Forcer l'apparition d'une console à l'écran
 */
void basculerVersConsole(Console * cons);

/*
 * Basculer vers la prochaine console virtuelle
 */
void basculerVersConsoleSuivante();

#endif  // MANUX_CONSOLES_VIRTUELLES

/*
 * Écriture sur une console
 */
size_t consoleEcrire(Fichier * f, void * buffer, size_t nbOctets);

#ifdef MANUX_APPELS_SYSTEME
/*
 * La fonction réalisant l'appel système  NBAS_ECRIRE_CONS 
 */
int sys_ecrireConsole(ParametreAS as, void * msg, int n);

#endif  // MANUX_APPELS_SYSTEME

#endif 
