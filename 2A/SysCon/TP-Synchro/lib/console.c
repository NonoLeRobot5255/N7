/**
 * @file  console.c
 * @brief Implantation des fonctions de base d'accés à la console.        
 *                                                                      
 *      Il s'agit ici aussi de quelque chose de très primitif. Chaque   
 *   console est une zone mémoire de la taille d'un écran et on tape    
 *   directement là-dedans. Pour rendre une console active, on permutte 
 *   simplement son adresse avec celle de l'écran physique. Du coup, les
 *   affichages se font réellement à l'écran.                               
 *                                                                            
 *                                                  (C) Manu Chaput 2000-2023 
 *                                                                            */
#include <manux/console.h>

#include <manux/errno.h>
#include <manux/appelsysteme.h>
#include <manux/memoire.h>      // NULL 
#include <manux/string.h>       // memcpy
#include <manux/debug.h>        // assert
#include <manux/temps.h>
#ifdef MANUX_KMALLOC
# include <manux/kmalloc.h>
#endif

/*
 * La console du noyau est celle "par défaut", sur laquelle seront
 * envoyés en particulier les messages du noyau (ceux affichés par
 * printk).
 */
static Console _consoleNoyau;

#ifdef MANUX_CONSOLES_VIRTUELLES

/**
 * @brief Pour les compter
 */
static int nombreDeConsoles = 0;

/**
 * En cas de gestion de consoles virtuelles, à tout moment, il n'y a
 * qu'une console "active" (ie visible). On en garde trace par une
 * variable globale.
 */
Console * consoleActive;

/**
 * Pour basculer d'une console à l'autre, on a besoin de stocker le
 * contenu des consoles non actives. Pour celle du noyau, la zone
 * mémoire est déclarée ici.
 */
static char copieEcranConsoleNoyau[2*MANUX_CON_COLONNES*MANUX_CON_LIGNES];

#ifdef MANUX_CLAVIER_CONSOLE
static char bufferClavierNoyau[4096]; // WARNING taille 1 page, pas joli de le harcoder !
#endif


#endif // MANUX_CONSOLES_VIRTUELLES

void consoleAffecterCouleurFond(Console * cons, Couleur coul)
{
   cons->attribut = (cons->attribut & 0x0F)|(coul<<4);
}

void consoleAffecterCouleurTexte(Console * cons, Couleur coul)
{
   cons->attribut = (cons->attribut & 0xF0)|(coul);
}

void consoleEffacer(Console * cons)
{
   int l, c;

   for (l = 0; l < cons->nbLignes; l++) {
      for (c = 0; c < cons->nbColonnes; c++) {
         cons->adresseEcran[2*(l*cons->nbColonnes+c)] = ' ';
         cons->adresseEcran[2*(l*cons->nbColonnes+c)+1] = cons->attribut;
      }
   }
   cons->ligne = 0;
   cons->colonne = 0;
}

void scrollUp(Console * cons)
/*
 * Remonté de l'écran d'une ligne
 */
{
   int c;

   /* Remontée du contenu de l'écran */
   memcpy(cons->adresseEcran,
	  cons->adresseEcran+2*cons->nbColonnes,
	  2*((cons->nbLignes-1)*cons->nbColonnes));
   
   /* On place une ligne d'espaces en bas de l'écran */
   for (c = 0; c < cons->nbColonnes; c++) {
      cons->adresseEcran[2*((cons->nbLignes-1)*cons->nbColonnes+c)] = ' ';
      cons->adresseEcran[2*((cons->nbLignes-1)*cons->nbColonnes+c)+1] = cons->attribut;
   }
}

void avancerLigne(Console * cons)
{
   assert(cons->nbLignes != 0);

   cons->ligne++;
   if (!(cons->ligne % cons->nbLignes)) {
      cons->ligne = cons->nbLignes - 1;
      scrollUp(cons);
   }
}

/*
 * L'attribut est là pour maintenir la compilation même sans
 * optimisation (donc pour le debogage) 
 */
 __attribute__((always_inline))
inline void consoleAfficherCaractere(Console * cons, char c)
{
   cons->adresseEcran[(cons->nbColonnes*cons->ligne+cons->colonne)*2] = c;
   cons->adresseEcran[(cons->nbColonnes*cons->ligne+cons->colonne)*2+1] = cons->attribut;
   cons->colonne++;

   // On avance d'un caratère
   assert(cons->nbColonnes != 0);
   if (!(cons->colonne % cons->nbColonnes)) {
      cons->colonne = 0;
      avancerLigne(cons);
   }
}

void consoleAfficherN(Console * cons, char * msg, int nbOctets)
{
  int controle;

  assert(nbOctets > 0);

#ifdef MANUX_CONSOLE_AVEC_MUTEX
   exclusionMutuelleEntrer(&cons->scAcces);
#endif

  assert(cons->nbColonnes != 0);

   while (nbOctets) {
      switch (*msg) {
         case '\n' :
            avancerLigne(cons);
            cons->colonne = 0;
         break;
         case ASCII_ESC :
            msg++;
            nbOctets--;
            if (*msg == 91){   // 91 = ASCII('[')
               do {
                  msg++;
                  controle = 0;
                  while((*msg <= '9') && (*msg >= '0')) {
                     controle = controle * 10 + * msg - '0';
                     msg++;nbOctets--;
	          }
                  switch (controle) {
                     case 0 : 
                        consoleAffecterCouleurTexte(cons, COUL_TXT_BLANC);
                        consoleAffecterCouleurFond(cons, COUL_FOND_NOIR);
                     break;
                     case 30 : 
                        consoleAffecterCouleurTexte(cons, COUL_TXT_NOIR);
                     break;
                     case 31 :
                        consoleAffecterCouleurTexte(cons, COUL_TXT_ROUGE);
                     break;
                     case 32 : 
                        consoleAffecterCouleurTexte(cons, COUL_TXT_VERT);
                     break;
                     case 34 :
                        consoleAffecterCouleurTexte(cons, COUL_TXT_BLEU);
                     break;
                     case 37 :
                        consoleAffecterCouleurTexte(cons, COUL_TXT_BLANC);
                     break;
                     case 40 : 
                        consoleAffecterCouleurFond(cons, COUL_FOND_NOIR);
                     break;
                     case 41 :
                        consoleAffecterCouleurFond(cons, COUL_FOND_ROUGE);
                     break;
                     case 42 : 
                        consoleAffecterCouleurFond(cons, COUL_FOND_VERT);
                     break;
                     case 44 :
                        consoleAffecterCouleurFond(cons, COUL_FOND_BLEU);
                     break;
                     case 47 :
                        consoleAffecterCouleurFond(cons, COUL_FOND_GRIS_CLAIR);
                     break;
                     default:
                     break;
		  }
               } while (*msg == 59); // 59 = ASCII(';') // WARNING !!!
            }
	    break;
         default :
            consoleAfficherCaractere(cons, *msg);
         break;
      }
      msg++;nbOctets--;
   }
#ifdef MANUX_CONSOLE_AVEC_MUTEX
   exclusionMutuelleSortir(&cons->scAcces);
#endif
}

void consoleAfficher(Console * cons, char * msg)
{
   int n = 0;
   while (msg[n])n++;
   consoleAfficherN(cons, msg, n);
}

/**
 * @brief Affichage d'un message sur la console noyau
 */
void consoleNoyauAfficher(char * msg)
{
   consoleAfficher(&_consoleNoyau, msg);
}

void consoleAfficherEntier(Console * cons, int n)
{
   char nombre[12];
   int i = 0;

   do {
      nombre[i] = n%10 + '0';
      n = n / 10;
      i++;
   } while (n);
   for (i--; i>=0; i--) {
      assert(cons->nbColonnes != 0);
      consoleAfficherCaractere(cons, nombre[i]);
   }
}

void consoleAfficherEntierHex(Console * cons, int nbOctets, uint32_t reg)
{
   char chiffre[17] = "0123456789abcdef";
   char nombre[2*nbOctets+2];
   int i = 0;

   for (i = 0; i<2*nbOctets; i++) {
      nombre[i] = chiffre[reg%16];
      reg = reg / 16;
   };
   nombre[i++] = 'x';
   nombre[i] = '0';
   for (; i>=0; i--) {
     assert(cons->nbColonnes != 0);
      consoleAfficherCaractere(cons, nombre[i]);
   }
}

#ifdef MANUX_CLAVIER_CONSOLE
void consoleSetClavier(Console * cons, void * buffer)
{
   // Le buffer accueillant le clavier
   cons->bufferClavier = buffer;
   cons->nbCarAttente = 0;
   cons->indiceProchainCar = 0;
}
#endif

/**
 * @brief Initialisation d'une nouvelle console virtuelle.
 *
 * Les espaces mémoire doivent avoir été alloués par ailleurs.
 */
void consoleInitialiser(Console * cons, char * adresseEcran)
{
   //! Adresse de la zone d'écran. L'affichage consiste en fait à
   //! écrire des choses dans la zone mémoire pointée
   cons->adresseEcran = adresseEcran;

#ifdef MANUX_CONSOLES_VIRTUELLES
   //! Chaque console a sa propre zone mémoire
   cons->adresseEcranCopie = adresseEcran;
#endif
   
   // La configuration de base
   cons->ligne = 0; 
   cons->colonne = 0;
   cons->nbLignes = MANUX_CON_LIGNES;
   cons->nbColonnes = MANUX_CON_COLONNES;
   cons->attribut = COUL_TXT_GRIS_CLAIR | COUL_FOND_NOIR;

   /* Initialisation du verrou */
#ifdef MANUX_CONSOLE_AVEC_MUTEX
   exclusionMutuelleInitialiser(&cons->scAcces);
#endif

   // Un peu de ménage
   consoleEffacer(cons);

#ifdef MANUX_CONSOLES_VIRTUELLES
   /* On l'insère après la console active dans la liste des consoles gérées */
   cons->suivante = consoleActive->suivante;
   consoleActive->suivante = cons;
   cons->precedente = consoleActive;
   cons->suivante->precedente = cons;
   cons->numero = nombreDeConsoles++;
#endif
#ifdef MANUX_CLAVIER_CONSOLE
   consoleSetClavier(cons, NULL);
#endif
}

#ifdef MANUX_CONSOLES_VIRTUELLES
/**
 * @brief : Création (avec allocation mémoire) d'une console
 */
Console * creerConsoleVirtuelle()
{
   Console * result;
   void    * page;

   //! On va tout mettre dans une page unique
   assert(2*MANUX_CON_COLONNES*MANUX_CON_LIGNES + sizeof(Console)
	  <= MANUX_TAILLE_PAGE);
   page = allouerPage();
   if (page == NULL) {
      paniqueNoyau("Plus de memoire !");
   }
   
   result = (Console *)page;

   //! On initialise ensuite la console
   consoleInitialiser(result, page + sizeof(Console));

#ifdef MANUX_CLAVIER_CONSOLE
   consoleSetClavier(result, allouerPage());
#endif

#ifdef MANUX_BASCULER_NOUVELLE_CONSOLE
   basculerVersConsole(result);
#endif
   
   return result;
}

/*
 * Basculer vers une console virtuelle. Attention, elle doit exister.
 */
void basculerVersConsole(Console * suivante)
{
   int i, l, c, a;

   assert(consoleActive != NULL);
   
   if (suivante == consoleActive)
      return;

   assert(suivante != NULL);
   
   // On sauvegarde l'écran physique dans la console active
   for (i=0; i < MANUX_CON_LIGNES*MANUX_CON_COLONNES*2; i++) { // WARNING utiliser bcopy
      consoleActive->adresseEcranCopie[i] = consoleActive->adresseEcran[i];
   }

   // On la désactive (à partir de maintenant, ce qui y est écrit
   // n'est plus visible à l'écran)
   consoleActive->adresseEcran = consoleActive->adresseEcranCopie;
   
   // On passe à la nouvelle CV 
   consoleActive = suivante;

#ifdef MANUX_CONSOLE_AVEC_MUTEX
   exclusionMutuelleEntrer(&consolesVirtuelles[consoleCourante]->scAcces);
#endif

   // On l'active (à partir de maintenant, ce qui y est écrit apparaît
   // directement à l'écran).
   consoleActive->adresseEcran = MANUX_CON_SCREEN;

   // On copie son état actuel sur l'écran
   for (i=0; i < MANUX_CON_LIGNES*MANUX_CON_COLONNES*2; i++) { // WARNING utiliser bopy
      consoleActive->adresseEcran[i] = consoleActive->adresseEcranCopie[i];
   }

   /* On affiche un bandeau d'info en haut */
   l = consoleActive->ligne;
   c = consoleActive->colonne;
   a = consoleActive->attribut;
   consoleActive->ligne = 0;
   consoleActive->colonne = 55;

   consoleActive->attribut = 0x1B;
   consoleAfficher(consoleActive, "Cons ");
   consoleAfficherEntierHex(consoleActive, 4,(uint32_t)consoleActive);
   consoleAfficher(consoleActive, "  t= ");
   consoleAfficherEntier(consoleActive, totalMinutesDansTemps(nbTopHorloge));
   consoleAfficher(consoleActive, ":");
   consoleAfficherEntier(consoleActive, secondesDansTemps(nbTopHorloge));
   consoleAfficher(consoleActive, " ");

   consoleActive->ligne = l;
   consoleActive->colonne = c;
   consoleActive->attribut = a;
   
#ifdef MANUX_CONSOLE_AVEC_MUTEX
   exclusionMutuelleSortir(&consoleActive->scAcces);
#endif
}

/*
 * Basculer vers la console suivante
 */
void basculerVersConsoleSuivante()
{
   assert(consoleActive != NULL);

   basculerVersConsole(consoleActive->suivante);
}

#endif  // CONSOLES_VIRTUELLES

#ifdef MANUX_CLAVIER_CONSOLE
#define min(a, b) (((a)<(b)) ? (a) : (b))

/**
 * @brief Lecture d'octets depuis une console
 */
int consoleLire(Console * cons, void * buffer, int nbOctets)
{
   // On ne peut pas en lire plus qu'il y en a !
   uint16_t nb = min(nbOctets, cons->nbCarAttente);
   uint16_t lu = 0;   // Le cumul des lectures
   uint16_t aLire;    // Combien on en lit à chaque passage

   while (lu < nb) {
     // On lit sur la "fin" du tableau circulaire
     aLire = min(nb-lu, 4096 - cons->indiceProchainCar);
     memcpy(buffer+lu,
	    cons->bufferClavier+cons->indiceProchainCar,
	    aLire);
     // On décompte cette lecture du buffer
     cons->indiceProchainCar = (cons->indiceProchainCar + aLire); // WARNING FAUX !
     cons->nbCarAttente = cons->nbCarAttente - aLire;

     //     printk("(0x%x) LIRE copie %d, ipc = %d, nb = %d\n", cons, aLire, cons->indiceProchainCar, cons->nbCarAttente);
     lu = lu + aLire;
   }

   return lu;
}

/**
 * @brief : Implantation de l'appel système de lecture pour la console
 *
 * On va chercher des données éventuellement mises à dispo par le
 * clavier. 
 */
size_t consoleFichierLire(Fichier * f, void * buffer, size_t nbOctets)
{
   Console * con = f->iNoeud->prive;

   return consoleLire(con, buffer, nbOctets);
}
#else
/**
 * En l'absence de clavier, rien à lire !
 */
size_t consoleFichierLire(Fichier * f, void * buffer, size_t nbOctets)
{
   return 0;
}
#endif

#ifdef MANUX_FICHIER
/**
 * @brief Ouverture d'une Console en tant que Fichier 
 *
 * WARNING : si vraiment rien à faire, on peut supprimer (la méthode
 * ouvrir peut ne pas être implantée)
 */
int consoleOuvrir(INoeud * iNoeud, Fichier * f, uint16_t fanions, uint16_t mode)
{
   return ESUCCES;
}

/**
 * @brief Écriture dans une Console vue comme un fichier
 */
size_t consoleEcrire(Fichier * f, void * buffer, size_t nbOctets)
{
   Console * con = f->iNoeud->prive;

   consoleAfficherN(con, buffer, nbOctets);

   return nbOctets; // WARNING
}

/**
 * @brief Déclaration des méthodes permettant de traiter une console
 * comme un fichier
 */
MethodesFichier consoleMethodesFichier = {
   .ouvrir = consoleOuvrir,
   .ecrire = consoleEcrire,
   .lire = consoleFichierLire
};
#endif // MANUX_FICHIER

/**
 * @brief Initialisation de la console du noyau
 *
 */
void initialiserConsoleNoyau()
{
   //! Le gros du travail est fait par initialiserConsole
   consoleInitialiser(&_consoleNoyau, MANUX_CON_SCREEN);

#ifdef MANUX_CLAVIER_CONSOLE
   consoleSetClavier(&_consoleNoyau, bufferClavierNoyau);
#endif
   
#ifdef MANUX_CONSOLES_VIRTUELLES
   //! Si on utilise plusieurs consoles, on doit pouvoir sauvegarder
   //! leur contenu, y compris pour celle du noyau
   _consoleNoyau.adresseEcranCopie = copieEcranConsoleNoyau;

   //! C'est la première, la seule pour le moment, on l'active donc et
   //! on la chaîne avec elle-même
   consoleActive = &_consoleNoyau;
   consoleActive->suivante = consoleActive;
   consoleActive->precedente = consoleActive;
#endif
}

/**
 * @brief Obtention d'un pointeur sur la console par défaut
 */
Console * consoleNoyau()
{
   return &_consoleNoyau;
}

#ifdef MANUX_FICHIER

void consoleInitialiserINoeud(INoeud * i, Console * c)
{
   i->typePeripherique.majeur = MANUX_CONSOLE_MAJEUR;
#ifdef MANUX_CONSOLES_VIRTUELLES
   i->typePeripherique.mineur = c->numero;
#else
   i->typePeripherique.mineur = 0;
#endif
   
   i->prive = c;
   i->methodesFichier = &consoleMethodesFichier;
}

/**
 * @brief :Initialisation du système de console. 
 * @param : iNoeudConsole (out) un INoeud décrivant la console par
 * défaut 
 */
int consoleInitialisationINoeud(INoeud * iNoeudConsole)
{
   //! On initialise la console
   initialiserConsoleNoyau();

   //! On initialise l'INoeud qui la décrit
   consoleInitialiserINoeud(iNoeudConsole,  &_consoleNoyau);

   return ESUCCES;
}

#   ifdef MANUX_KMALLOC
/**
 * @brief : Création d'un iNoeud permettant de manipuler une console
 * @param : c (in) pointeur sur la console
 * @return : pointeur sur un INoeud
 */
INoeud * consoleCreerINoeud(Console * c)
{
   INoeud * result;

   result = kmalloc(sizeof(INoeud));

   if (result) {
      //! On initialise l'INoeud qui la décrit
      consoleInitialiserINoeud(result, c);
   }
   
   return result;
}

#   endif // MANUX_KMALLOC
#endif
/**
 * Initialisation du système de console. 
 */
int consoleInitialisation()
{
   initialiserConsoleNoyau();
   
   return ESUCCES;
}

#ifdef MANUX_APPELS_SYSTEME
/*
 * L'implantation de l'AS ecrireConsole
 */
int sys_ecrireConsole(ParametreAS as, void * msg, int n)
{
   //! Si on a attribué une console à  chaque tâche, on va la chercher
   //! Si ce n'est pas le cas, on prend la seule console, celle du
   //! noyau
#if defined(MANUX_TACHES) && defined(MANUX_TACHE_CONSOLE)
   assert(tacheEnCours != NULL);
   Console * cons = tacheEnCours->console;
#else
   Console * cons = &_consoleNoyau;
#endif
   
   assert(cons != NULL);
   consoleAfficherN(cons, msg, n);

   return n;
}
#endif // MANUX_APPELS_SYSTEMES
