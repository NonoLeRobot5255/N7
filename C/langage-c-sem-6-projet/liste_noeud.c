#define _GNU_SOURCE
#include "liste_noeud.h"
#include <stdlib.h>
#include <math.h>
#include <stdbool.h>

liste_noeud_t* creer_liste(){
    liste_noeud_t* liste = (liste_noeud_t*)malloc(sizeof(liste_noeud_t));
    if (liste != NULL){
        liste->suiv = NULL;
        return liste;
    }
}

void detruire_liste(liste_noeud_t* liste_ptr){
    if(liste_ptr != NULL){
        liste_noeud_t* courant = liste_ptr;
        while(courant != NULL){
            liste_noeud_t* suivant = courant->suiv;
            free(courant);
            courant = suivant;
        }
    }
}

bool est_vide_liste(const liste_noeud_t* liste){
    return liste->suiv == NULL;
}

bool contient_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    liste_noeud_t* courant = liste->suiv;
    while(courant != NULL){
        if(courant->n == noeud){
            return true;
        }
        courant = courant->suiv;
    }
    return false;
}

bool contient_arrete_liste(const liste_noeud_t* liste, noeud_id_t source, noeud_id_t destination){
    liste_noeud_t* courant = liste->suiv;
    while(courant != NULL){
        if(courant->n == destination && courant->prec == source){
            return true;
        }
        courant = courant->suiv;
    }
    return false;
}

float distance_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    liste_noeud_t* courant = liste->suiv;
    while(courant != NULL){
        if(courant->n == noeud){
            return courant->dist;
        }
        courant = courant->suiv;
    }
    return INFINITY;
}

liste_noeud_t* precedent_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    liste_noeud_t* courant = liste->suiv;
    while(courant != NULL){
        if(courant->n == noeud){
            return courant.prec;
        }
        courant = courant->suiv;
    }
    return NULL;
}

noeud_id_t min_noeud_liste(const liste_noeud_t* liste){
    liste_noeud_t* courant = liste->suiv;
    noeud_id_t min = NO_ID;
    float min_dist = INFINITY;
    while(courant != NULL){
        if(courant->dist < min_dist){
            min = courant->n;
            min_dist = courant->dist;
        }
        courant = courant->suiv;
    }
    return min;
}

void inserer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance){
    liste_noeud_t* courant = liste;
    while(courant->suiv != NULL){
        courant = courant->suiv;
    }
    courant->suiv = (liste_noeud_t*)malloc(sizeof(liste_noeud_t));
    courant = courant->suiv;
    courant->n = noeud;
    courant->prec = precedent;
    courant->dist = distance;
    courant->suiv = NULL;
}

void changer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance){
    liste_noeud_t* courant = liste->suiv;
    while(courant != NULL){
        if(courant->n == noeud){
            courant->prec = precedent;
            courant->dist = distance;
            return;
        }
        courant = courant->suiv;
    }
    inserer_noeud_liste(liste, noeud, precedent, distance);
}

void supprimer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud){
    liste_noeud_t* courant = liste;
    while(courant->suiv != NULL){
        if(courant->suiv->n == noeud){
            liste_noeud_t* suivant = courant->suiv->suiv;
            free(courant->suiv);
            courant->suiv = suivant;
            return;
        }
        courant = courant->suiv;
    }
}