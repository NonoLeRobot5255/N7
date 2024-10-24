// This file is part of dijkstra.
// 
// dijkstra is free software: you can redistribute it and/or modify it under 
// the terms of the GNU General Public License as published by the Free Software 
// Foundation, either version 3 of the License, or (at your option) any later 
// version.
// 
// dijkstra is distributed in the hope that it will be useful, but WITHOUT ANY 
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR 
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
// 
// You should have received a copy of the GNU General Public License along with 
// dijkstra. If not, see <https://www.gnu.org/licenses/>.
//
// dijkstra - Copyright (c) 2024 Guillaume Dupont
// Contact: <guillaume.dupont@toulouse-inp.fr>
/**
 * @file dijkstra_event.h
 * @brief Module complémentaire pour interfacer la fonction dijkstra avec le
 * reste de l'application.
 *
 * Ce module n'est à consulter que si vous réalisez le travail (optionnel) décrit dans le
 * classeur 4 (optionnel lui aussi).
 *
 * Ne vous souciez pas de ce qui se passe ici si vous n'avez pas le classeur 4 sous les yeux...
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef DIJKSTRA_EVENT_H
#define DIJKSTRA_EVENT_H

#include "graphe.h"

/**
 * Un enregistrement qui contient des fonctions que la fonction @ref dijkstra doit appeler
 * à certaines étapes du calcul.
 *
 * L'utilisateur fourni typiquement certaines ou plusieurs fonctions et @ref dijkstra se charge
 * de les appeler au bon moment, et en passant les user data données initialement (argument
 * de type `void*` de chaque fonction).
 *
 * On doit pouvoir laisser un champ à NULL si on n'utilise pas la fonction.
 *
 * Cette façon de procéder ressemble beaucoup à un patron de conception type _listener_ (ou
 * _observer_), sauf qu'on est pas en objet ! Néanmoins le principe est le même et est inspiré
 * de la programmation réactive/événementielle : l'appel d'une de ces fonction correspond en
 * quelques sortes à l'émission d'un événement, et le code exécuté au comportement attendu à
 * la réception de l'événement.
 */
struct dijkstra_event_t {
    /** Fonction appelée lorsque l'algorithme visite un noeud (début de la boucle principale).
     * Les arguments sont : le noeud visité et les user data.
     */
    void (*on_visiting)(noeud_id_t,void*);
    /** Fonction appelée lorsque l'algorithme a terminé de visiter le noeud (fin de la boucle principale).
     * Les arguments sont : le noeud visité et les user data.
     */
    void (*on_visited)(noeud_id_t,void*);
    /** Fonction appelée lorsque l'algorithme explore un voisin (boucle intérieure, celle qui parcourt les voisins).
     * Les arguments sont, dans l'ordre : le noeud courant, le noeud voisin et les user data
     */
    void (*on_exploring)(noeud_id_t,noeud_id_t,void*);
    /** Fonction appelée lorsque l'algorithme marque le noeud comme "à visiter" (boucle intérieure, celle qui parcourt les voisins).
     * Les arguments sont : le noeud ajouté à AVisiter et les user data.
     */
    void (*on_marking)(noeud_id_t,void*);
    /** Fonction appelée à chaque fois que le chemin change lors de la construction du chemin (lorsqu'on ajoute un
     * noeud a priori).
     * Les arguments sont : le chemin en cours de construction et les user data.
     */
    void (*on_path_build)(liste_noeud_t*,void*);
};

#endif // DIJKSTRA_EVENT_H



