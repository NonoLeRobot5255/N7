/*
 * Utilise-t-on un mécanisme de journal des messages du noyau ?
 */
#define MANUX_JOURNAL

/*
 * Le journal utilise la console via l'interface fichier
 * traditionnelle (read/write). Mais dans certaines phases de debug,
 * ça peut s'avérer utile de contourner ça et de l'accéder
 * directement.
 */
#define MANUX_JOURNAL_DIRECT_CONSOLE

/**
 * On affichera les messages d'un niveau plus faible ou égal à
 * MANUX_JOURNAL_NIVEAU_DEFAUT
 */
#define MANUX_JOURNAL_NIVEAU_DEFAUT       7

