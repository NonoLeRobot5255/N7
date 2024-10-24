#ifndef DIJKSTRA_H
#define DIJKSTRA_H

#include "graphe.h"
#include "liste_noeud.h"

/**
 * dijkstra - Calcul le plus court chemin dans un graphe, entre les noeuds donnés.
 * La fonction retourne la distance calculée, et peuple le chemin passé en paramètre
 * (si non NULL) avec le chemin correspondant.
 *
 * Pré-conditions : 
 *   - graphe non NULL
 *   - source référence un noeud du graphe
 *   - destination référence un noeud du graphe
 *   - source et destination sont connectés
 * Post-conditions :
 *   - retour >= 0.0
 *   - si chemin != NULL, *chemin contient un chemin connexe de source à destination
 *     La fonction se charge d'allouer le chemin sur le tas (et l'utilisateur se charge de le
 *     détruire).
 *
 * @param graphe [in] graphe dans lequel calculer le chemin
 * @param source identifiant du noeud de départ
 * @param destination identifiant du noeud de destination 
 * @param chemin [out] pointeur sur une variable de type liste_noeud_t* pour recevoir
 *   le chemin calculé
 * @return distance minimale entre le noeud source et destination, via le graphe
 */
float dijkstra(
        const struct graphe_t* graphe, 
        noeud_id_t source, noeud_id_t destination, 
        liste_noeud_t** chemin);


#endif // DIJKSTRA_H


