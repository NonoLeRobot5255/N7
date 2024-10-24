/**
 * @file journal.c
 * @brief Implantation des outils de journalisation des messages du noyau.     
 *
 * Il y a des trucs pas très jolis, par exemple l'accès direct à la
 * console. A priori elle devrait être utilisée uniquement via des read/write
 * mais c'est pas plus mal de pouvoir les contourner pour certains
 * debugages. Le truc, c'est que le journal ne la connaît que comme un
 * iNoeud (même s'il sait aller y trouver l'accès direct). Du coup,
 * printk doit passer par le journal, ce qui est bien, mais pour
 * contourner tout ça, j'ai encore un accès direct pas joli dans
 * printk. A supprimer un jour j'espère. Si en particulier la macro
 * MANUX_JOURNAL_DIRECT_CONSOLE ne sert pas trop.
 *
 *                                                  (C) Manu Chaput 2002-2023 
 */
#include <manux/config.h>
#include <manux/memoire.h>  // NULL
#include <manux/journal.h>
#include <manux/string.h>   // strlen

/**
 * Le journal utilise la console en passant par l'interface fichier
 * qu'elle propose si cette interface est configurée.
 * Si ce n'est pas le cas, la console est accédée directement.
 */
#ifdef MANUX_FICHIER
Fichier _consoleFichier; // Pour éviter un kmalloc pour le moment
Fichier * consoleFichier = NULL;
#else
Console * consoleJournal = NULL;
#endif

/**
 * Il faut pourvoir se prémunir si on souhaite utiliser printk avant
 * l'initialisation du journal.
 */
static booleen journalInitialise = FALSE;

//static ExclusionMutuelle emj;

#ifdef MANUX_FICHIER
/**
 * Le journal utilise également éventuellement un second fichier, par
 * exemple pour envoyer sur l'écran de l'hôte via un virtio-console,
 * ou pour stocker dans un fichier pour analyse post-mortem.
 */
Fichier * fichierJournal = NULL;

/**
 * @brief Initialisation du journal en profitant de l'interface
 * fichier
 * WARNING : ne pas utiliser le même nom que sans fichier
 */
void journalInitialiserInoeud(INoeud * iNoeudConsole)
{
    //   initialiserExclusionMutuelle(&emj);
    //   entrerExclusionMutuelle(&emj);

   consoleFichier = &_consoleFichier;
   fichierOuvrir(iNoeudConsole, consoleFichier, O_WRONLY, 0);

   // Affichons un petit message   
   consoleNoyauAfficher("Journal+f de ManuX-32 \n");

   // A partir de maintenant, le journal est opérationnel
   journalInitialise = TRUE;
   
   //   sortirExclusionMutuelle(&emj);
}

void journalAffecterFichier(Fichier * pc)
{
   fichierJournal = pc;
}

#endif

/**
 * @brief Initialisation du journal sans interface fichier
 */
void journalInitialiser()
{
    //   initialiserExclusionMutuelle(&emj);
    //   entrerExclusionMutuelle(&emj);

   // consoleAffecterCouleurTexte(consoleJournal, COUL_TXT_BLANC);

   // Affichons un petit message   
   consoleNoyauAfficher("Journal de ManuX-32\n");

   // A partir de maintenant, le journal est opérationnel
   journalInitialise = TRUE;
   
   //   sortirExclusionMutuelle(&emj);
}

/**
 * @brief Journalisation d'un message avec un niveau d'urgence
 */
void journaliserNiveau(booleen console, booleen fichier,
		       uint8_t niveau,
		       char * message)
{
    //   entrerExclusionMutuelle(&emj);

   // Sur la console
   if ((console) && (niveau <= MANUX_JOURNAL_NIVEAU_DEFAUT)) {
#ifdef MANUX_FICHIER
      // Si le fichier a été ouvert, on y écrit ...
      if (consoleFichier) { 
         fichierEcrire(consoleFichier, message, strlen(message));
      // ... mais s'il n'est pas encore ouvert (pas initialisé), on
      // passe directement par la console
      } else {
         consoleNoyauAfficher(message);
      }
#else
      consoleNoyauAfficher(message);
#endif
   }

#ifdef MANUX_FICHIER
   // Sur le fichier s'il y en a un
   if (fichierJournal) {
      if ((fichier) && (niveau <= MANUX_JOURNAL_NIVEAU_DEFAUT)) {
	fichierEcrire(fichierJournal, message, strlen(message));   
      }
   }
#endif
   
  //   sortirExclusionMutuelle(&emj);
}

/**
 * @brief Gestion des niveaux d'affichage
 */
void aiguillerMessage(char ** message,
		      booleen * cons, booleen * fic, uint8_t * niv)
{
   int longueurPrefixe = 0;
   *cons = FALSE;
   *fic = FALSE;
   *niv = 0;

   switch ((*message)[0]) {
      case '[' :
         *cons = TRUE;
      break ;
      case '{' :
         *cons = TRUE;
      case '(' :
         *fic = TRUE;
      break ;
      default :
         *cons = TRUE;  // WARNING defaut
         *fic = TRUE;
      return;
   };

   longueurPrefixe ++;
   if (((*message)[1] <= '9') && ((*message)[1] >= '0')) {
      *niv = (*message)[1] - '0';
      longueurPrefixe ++;

      if (((*message)[2] == ')') || ((*message)[2] == '}') || ((*message)[2] == ']')) {
         longueurPrefixe ++;
      }
   }
   (*message) += longueurPrefixe;
}

/**
 * @brief Journalisation d'un message
 */
void journaliser(char * message)
{
   booleen console; //< affiche-t-on le message sur la console ?
   booleen fichier; //< envoie-t-on le message sur un fichier de log ?
   uint8_t niveau;  //< quel est le niveau de criticité ?

   // On détermine où il doit être envoyé pour affichage
   aiguillerMessage(&message, &console, &fichier, &niveau);

   // On l'envoie
   journaliserNiveau(console, fichier, niveau, 
		     message);
}

/**
 * Pour que printk puisse savoir
 * WARINING apparemment inutile
 */
booleen journalOperationnel()
{
   return journalInitialise;
}


