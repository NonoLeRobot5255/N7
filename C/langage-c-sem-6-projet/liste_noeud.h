#include "graphe.h"
#include <stdbool.h>

// TODO : type liste_noeud_t
typedef struct liste_noeud_t liste_noeud_t;
// TODO : typedef
struct liste_noeud_t{
    noeud_id_t n;
    float dist;
    noeud_id_t prec;
    struct liste_noeud_t* suiv;
};

/**
 * creer_liste : crée une liste de noeuds, initialement vide
 *
 * Post-conditions : `r = creer_liste()` => `r != NULL`, `est_vide_liste(r)`
 * @return liste nouvellement créée (de type liste_noeud_t)
 */
liste_noeud_t* creer_liste();

/**
 * detruire_liste : détruit la liste passée en paramètre
 *
 * Pré-conditions : liste_ptr != NULL
 * Post-conditions : *liste_ptr == NULL
 *
 * @param liste_ptr pointeur sur la liste à détruire
 */
void detruire_liste(liste_noeud_t* liste_ptr);

/**
 * est_vide_liste : test si la liste passée en paramètre est vide
 *
 * Pré-conditions : liste != NULL
 *
 * @param liste [in] liste à tester
 * @return vrai ssi la liste ne contient aucun élément
 */
bool est_vide_liste(const liste_noeud_t* liste);

/**
 * contient_noeud_liste : test si le noeud donné appartient à la liste donnée.
 * 
 * Pré-conditions : liste != NULL
 *
 * @param liste [in] liste à parcourir
 * @param noeud noeud à rechercher
 * @return vrai ssi noeud est dans liste
 */
bool contient_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud);

/**
 * contient_arrete_liste : test si l'arrête donnée appartient à la liste donnée.
 * L'arrête (source, destination) appartient à la liste ssi destination appartient à liste
 * et si prec(destination) == source.
 *
 * Pré-conditions : liste != NULL
 *
 * @param liste [in] liste à parcourir
 * @param source noeud source de l'arrête
 * @param destination noeud destination de l'arrête
 * @return vrai ssi l'arrête (source,destination) est dans liste
 */
bool contient_arrete_liste(const liste_noeud_t* liste, noeud_id_t source, noeud_id_t destination);

/**
 * distance_noeud_liste : récupère la distance associée au noeud donné dans la liste donnée.
 * Si le noeud n'existe pas dans la liste, retourne `INFINITY`.
 *
 * Pré-conditions : liste != NULL
 * Post-conditions : `contient_noeud_liste(liste, noeud)` <=> `distance_noeud_liste(liste, noeud) != INFINITY`
 *
 * @param liste [in] liste à parcourir
 * @param noeud noeud dont on veut la distance
 * @return distance associée à noeud dans liste ou INFINITY si noeud n'est pas dans liste
 */
float distance_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud);

/**
 * precedent_noeud_liste : récupère le noeud précédent associé au noeud donné dans la liste donnée.
 * Si le noeud n'existe pas, retourne `NO_ID`.
 * 
 * Pré-conditions : liste != NULL
 * Post-conditions : `!contient_noeud_liste(liste, noeud)` => `precedent_noeud_liste(liste, noeud) = NO_ID`
 *
 * @param liste [in] liste à parcourir
 * @param noeud noeud dont on veut le précédent
 * @return précédent associé au noeud dans la liste (ou `NO_ID` si noeud n'est pas dans liste)
 */
liste_noeud_t* precedent_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud);

/**
 * min_noeud_liste : trouve le (un) noeud de la liste dont la distance associée est la plus petite,
 * ou renvoie `NO_ID` si la liste est vide.
 *
 * Pré-conditions : liste non NULL
 * Post-conditions : `n = min_noeud_liste(liste) && n != NO_ID` =>
 *   pour tout `n', contient_noeud_liste(liste, n')`, `distance_noeud_liste(liste, n) <= distance_noeud_liste(liste, n')`
 *
 * @param liste [in] liste à parcourir
 * @return noeud qui minimise la distance, ou `NO_ID` si pas de noeud
 */
noeud_id_t min_noeud_liste(const liste_noeud_t* liste);

/**
 * inserer_noeud_liste : insère le noeud donné dans la liste
 *
 * Pré-conditions : liste != NULL
 *
 * @param liste [in,out] liste dans laquelle insérer l'élément
 * @param noeud noeud à insérer (caractérisé par son identifiant)
 * @param precedent noeud précédent du noeud à insérer (prec(n))
 * @param distance distance du noeud à insérer (dist(n))
 */
void inserer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance);

/**
 * changer_noeud_liste : modifie les valeurs associées au noeud donné dans la liste donnée.
 * Si le noeud n'est pas dans la liste, il est ajouté.
 *
 * Pré-conditions : liste != NULL
 * Post-conditions :
 *   - `contient_noeud_liste(liste, noeud)`
 *   - `distance_noeud_liste(liste, noeud) == distance`
 *   - `precedent_noeud_liste(liste, noeud) == precedent`
 *
 * @param liste [in,out] liste à modifier
 * @param noeud noeud à modifier
 * @param precedent nouveau noeud précédent pour noeud
 * @param distance nouvelle distance pour noeud
 */
void changer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance);

/**
 * supprimer_noeud_liste : supprime le noeud donné de la liste. Si le noeud n'est pas dans la liste,
 * ne fait rien.
 *
 * Pré-conditions : liste != NULL
 * Post-conditions : après `supprimer_noeud_liste(liste, n)` : `!contient_noeud_liste(liste, n)`
 *
 * @param liste [in,out] liste à modifier
 * @param noeud noeud à supprimer de liste
 */
void supprimer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud);


