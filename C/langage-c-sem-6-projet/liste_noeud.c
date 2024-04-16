#include "liste_noeud.h"
#include <stdlib.h>
#include <math.h>

liste_noeud_t* creer_liste(){
    liste_noeud_t* liste = (liste_noeud_t*)malloc(sizeof(liste_noeud_t));
    if(liste != NULL){
        liste->suiv = NULL;
    } 
    return liste;
}

void detruire_liste(liste_noeud_t* liste_ptr){
    while (liste_ptr!= NULL && liste_ptr->suiv != NULL)
    {
        liste_noeud_t* temp = liste_ptr;
        liste_ptr = liste_ptr->suiv;
        free(temp);
    }
    if (liste_ptr != NULL){ 
        free(liste_ptr);
    } 
}

bool est_vide_liste(const liste_noeud_t* liste_ptr){
    return liste_ptr->suiv == NULL;
}

bool contient_noeud_liste(const liste_noeud_t* liste, noeud_id_t noeud){
    if (liste->suiv == NULL && liste->n != noeud){
        return false;
    }
    else{
        if (liste->n == noeud){
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
        if (liste->n == source){
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
    while (liste->suiv != NULL)
    {
        if (liste->suiv->n == noeud)
        {
            return liste->n;
        }
        liste = liste->suiv;
    }
    return NO_ID;
}

noeud_id_t min_noeud_liste(const liste_noeud_t* liste){
    if (liste->suiv == NULL){
        return NO_ID;
    }
    else{
        noeud_id_t min = liste->n;
        float min_dist = liste->dist;
        while (liste->suiv != NULL)
        {
            if (liste->dist < min_dist){
                min = liste->n;
                min_dist = liste->dist;
            }
            liste = liste->suiv;
        }
        return min;
    }
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
        nouveau_noeud->n = noeud;
        nouveau_noeud->prec = precedent;
        nouveau_noeud->dist = distance;

        // Mettre à jour les liaisons
        nouveau_noeud->suiv = courant->suiv;
        courant->suiv = nouveau_noeud;
    } else {
        // Gérer le cas où le nœud précédent n'est pas trouvé
        // Peut-être imprimer un message d'erreur ou gérer différemment selon votre besoin
       return NO_ID;
    }
}

void changer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud, noeud_id_t precedent, float distance){
    while (liste->suiv != NULL)
    {
        if (liste->n == noeud)
        {
            liste->prec = precedent;
            liste->dist = distance;
        }
        liste = liste->suiv;
    }
    inserer_noeud_liste(liste,noeud,precedent,distance);
}

void supprimer_noeud_liste(liste_noeud_t* liste, noeud_id_t noeud){
    while (liste->suiv != NULL)
    {
        if (liste->suiv->n == noeud)
        {
            liste->suiv = liste->suiv->suiv;
        }
        liste = liste->suiv;
    }
}
