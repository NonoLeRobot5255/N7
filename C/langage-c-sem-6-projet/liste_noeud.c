#include "liste_noeud.h"
#include <stdlib.h>
#include <math.h>

liste_noeud_t* creer_liste(){
    liste_noeud_t* liste = (liste_noeud_t*)malloc(sizeof(liste_noeud_t));
    if (liste != NULL) {
        liste->n = NO_ID;
        liste->prec = NO_ID;
        liste->dist = INFINITY;
        liste->suiv = NULL;
    }
    return liste;
}

void detruire_liste(liste_noeud_t* liste_ptr){
    liste_noeud_t* courant = liste_ptr;
    liste_noeud_t* suivant = NULL;

    while (courant != NULL) {
        suivant = courant->suiv;
        free(courant);
        courant = suivant;
    }
}

bool est_vide_liste(const liste_noeud_t* liste_ptr){
    return liste_ptr == NULL || liste_ptr->suiv == NULL;
}

bool contient_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    while (liste != NULL) {
        if (liste->n == noeud) {
            return true;
        }
        liste = liste->suiv;
    }
    return false;
}

bool contient_arrete_liste(const liste_noeud_t* liste, noeud_id_t source, noeud_id_t destination){
    while (liste != NULL) {
        if (liste->n == source && liste->suiv != NULL && liste->suiv->n == destination) {
            return true;
        }
        liste = liste->suiv;
    }
    return false;
}

float distance_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud) {
    while (liste != NULL) {
        if (liste->n == noeud) {
            return liste->dist;
        }
        liste = liste->suiv;
    }
    return INFINITY;
}

noeud_id_t precedent_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    while (liste != NULL && liste->suiv != NULL) {
        if (liste->suiv->n == noeud) {
            return liste->n;
        }
        liste = liste->suiv;
    }
    return NO_ID;
}

noeud_id_t min_noeud_liste(const liste_noeud_t* liste){
    if (liste == NULL || liste->suiv == NULL) {
        return NO_ID;
    }

    noeud_id_t min = liste->n;
    float min_dist = liste->dist;
    while (liste != NULL) {
        if (liste->dist < min_dist){
            min = liste->n;
            min_dist = liste->dist;
        }
        liste = liste->suiv;
    }
    return min;
}

void inserer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance) {
    liste_noeud_t* courant = liste;

    // Recherche du nœud précédent
    while (courant != NULL && courant->n != precedent) {
        courant = courant->suiv;
    }

    // Si le nœud précédent est trouvé, insérer le nouveau nœud
    if (courant != NULL) {
        liste_noeud_t* nouveau_noeud = (liste_noeud_t*)malloc(sizeof(liste_noeud_t));
        if (nouveau_noeud != NULL) {
            nouveau_noeud->n = noeud;
            nouveau_noeud->prec = precedent;
            nouveau_noeud->dist = distance;

            // Mettre à jour les liaisons
            nouveau_noeud->suiv = courant->suiv;
            courant->suiv = nouveau_noeud;
        } else {
            // Gérer le cas où l'allocation de mémoire a échoué
            // Peut-être imprimer un message d'erreur ou gérer différemment selon votre besoin
        }
    }
}

void changer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance){
    while (liste != NULL) {
        if (liste->n == noeud) {
            liste->prec = precedent;
            liste->dist = distance;
            return;
        }
        liste = liste->suiv;
    }
    inserer_noeud_liste(&liste, noeud, precedent, distance);
}

void supprimer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud){
    liste_noeud_t* courant = liste;
    liste_noeud_t* precedent = NULL;

    // Si le nœud à supprimer est en tête de liste
    if (courant != NULL && courant->n == noeud) {
        liste = courant->suiv;
        free(courant);
        return;
    }

    // Recherche du nœud à supprimer
    while (courant != NULL && courant->n != noeud) {
        precedent = courant;
        courant = courant->suiv;
    }

    // Si le nœud est trouvé dans la liste
    if (courant != NULL) {
        precedent->suiv = courant->suiv;
        free(courant);
    }
}
