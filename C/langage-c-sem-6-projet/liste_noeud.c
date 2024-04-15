#define _GNU_SOURCE
#include "liste_noeud.h"
#include <stdlib.h>
#include <math.h>

liste_noeud_t creer_liste(){
    liste_noeud_t* liste = (liste_noeud_t*)malloc(sizeof(liste_noeud_t));
    liste_noeud_t* suiv = NULL;
}

void detruire_liste(liste_noeud_t liste_ptr){
    liste_ptr = NULL;
    free(liste_ptr);
}

bool est_vide_liste(const liste_noeud_t liste_ptr){
    return liste_ptr.suiv == NULL;
}

bool contient_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    if (liste->suiv == NULL && liste->n != noeud){
        return false;
    }
    else{
        if (liste-> n == noeud){
            return true;
        }
        else{
            return contient_noeud_liste(liste->suiv,noeud);
        }
    }
}

bool contient_arrete_liste(const liste_noeud_t* liste, noeud_id_t source, noeud_id_t destination){
    if (liste->suiv == NULL && liste->n != destination){
        return false;
    }
    else{
        if (liste-> n == source){
            if (liste->suiv->n == destination ){
                return true;
            }
            else{
                return contient_arrete_liste(liste->suiv,source,destination);
            }
        }
        else{
            return contient_arrete_liste(liste->suiv,source,destination);
        }
    }
}

float distance_noeud_liste(const liste_noeud_t liste, noeud_id_t noeud) {
    while (liste->suiv != NULL)
    {
        if (liste->n == noeud)
        {
            return liste.dist;
        }
        liste = liste->suiv;
    }
    return INFINITY;
    
}