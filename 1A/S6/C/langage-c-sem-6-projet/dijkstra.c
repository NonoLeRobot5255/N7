#include "dijkstra.h"
#include <stdlib.h>

/**
 * construire_chemin_vers - Construit le chemin depuis le noeud de départ donné vers le
 * noeud donné. On passe un chemin en entrée-sortie de la fonction, qui est mis à jour
 * par celle-ci.
 *
 * Le noeud de départ est caractérisé par un prédécesseur qui vaut `NO_ID`.
 *
 * Ce sous-programme fonctionne récursivement :
 *  1. Si le noeud a pour précédent `NO_ID`, on a fini (c'est le noeud de départ, le chemin de
 *     départ à départ se compose du simple noeud départ)
 *  2. Sinon, on construit le chemin du départ au noeud précédent (appel récursif)
 *  3. Dans tous les cas, on ajoute le noeud au chemin, avec les caractéristiques associées dans visites
 *
 * @param chemin [in/out] chemin dans lequel enregistrer les étapes depuis le départ vers noeud
 * @param visites [in] liste des noeuds visités créée par l'algorithme de Dijkstra
 * @param noeud noeud vers lequel on veut construire le chemin depuis le départ
 */
// TODO: construire_chemin_vers


float dijkstra(
    const struct graphe_t* graphe, 
    noeud_id_t source, noeud_id_t destination, 
    liste_noeud_t** chemin) {
        liste_noeud_t* aVisite = creer_liste();
        liste_noeud_t* Visite = creer_liste();
        inserer_noeud_liste(aVisite, source , NO_ID, 0.0);
        while( !est_vide_liste(aVisite)){
            noeud_id_t nc = min_noeud_liste(aVisite);
            inserer_noeud_liste(Visite, nc , precedent_noeud_liste(aVisite, nc), distance_noeud_liste(aVisite, nc));
            supprimer_noeud_liste(aVisite, nc);
            noeud_id_t* voisins;
            noeuds_voisins(graphe, nc, voisins)
            for (int i=0;i<nombre_voisins(graphe, nc);i++){
                if (!contient_noeud_liste(Visite, voisins[i])){
                    float disttot = distance_noeud_liste(Visite, nc) + noeud_distance(graphe,nc, voisins[i]);
                    float distact = distance_noeud_liste(aVisite, voisins[i]);
                    if (disttot<distact){
                        if (!contient_noeud_liste(aVisite, voisins[i])){
                            inserer_noeud_liste(aVisite, voisins[i] , nc, disttot);
                        }
                        else{
                            changer_noeud_liste(aVisite, voisins[i], nc, disttot);
                        }
                    }

                }
            }
        }
}


