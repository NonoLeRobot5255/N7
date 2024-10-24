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
 * @file graphrep.h
 * @brief Module graphrep qui définit un composant de représentation de graphe, à embarquer
 * dans une @ref window_t.
 *
 * Les noeuds sont représentés avec des cercles et les arcs par des flèches incurvées.
 *
 * Le composnat permet de mettre en valeur un chemin, et réagit lorsqu'on survole les noeuds.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef GRAPHREP_H
#define GRAPHREP_H

#include <SDL2/SDL.h>
#include "graphe.h"
#include "liste_noeud.h"
#include "viewport.h"
#include "window.h"

/** Paramètre de représentation : taille des noeuds */
#define NODE_SIZE       30
/** Paramètre de représentation : espace entre le noeud et les arcs */
#define NODE_SKIP       0
/** Paramètre de représentation : largeur du trait pour les arcs (non fonctionnel) */
#define EDGE_WIDTH      2
/** Distance au centre du noeud à partir de laquelle la tooltip est affichée */
#define TOOLTIP_THRESH  30.0

/*
 * Type (abstrait) du composant de représentation de graphe.
 */
struct graphrep_t;

/**
 * Crée un composant de représentation de graphe pour la fenêtre donnée et avec le graphe donné.
 * Le composant représente le graphe sur la zone réelle donnée (area) et avec le viewport donné, qui
 * convertit les coordonnées des noeuds en coordonnées d'écran. Cela permet de représenter n'importe quel
 * système de coordonnée du graphe.
 *
 * Pré-conditions : window non NULL, graph non NULL
 *
 * @param window fenêtre dans laquelle mettre le composant
 * @param graph graphe à représenter
 * @param area zone de l'écran où le composant est représenté
 * @param viewport transformation entre écran et système de coordonnées du graphe
 * @return composant de représentation, alloué sur le tas
 */
struct graphrep_t* create_graphrep(struct window_t* window, struct graphe_t* graph, SDL_Rect area, viewport_t viewport);

/**
 * Crée un composant de représentation de graphe pour la fenêtre donnée et avec le graphe donné, pour
 * la zone d'écran donné. Le viewport est calculé automatiquement à partir de l'aire occupée par le graphe
 * et de la zone donnée.
 *
 * Pré-conditions : window non NULL, graph non NULL
 *
 * @param window fenêtre dans laquelle représenter le composant
 * @param graph graphe à représenter
 * @param area zone de l'écran dans laquelle représenter le graphe
 * @return composant de représentation, alloué sur le tas
 */
struct graphrep_t* create_graphrep_with_vp(struct window_t* window, struct graphe_t* graph, SDL_Rect area);

/**
 * Détruit le composant de représentation de graphe (libère toute la mémoire allouée).
 * Ceci ne libère pas le graphe.
 *
 * Pré-conditions : graphrep non NULL, graphrep pas déjà détruit
 * Post-conditions : *graphrep == NULL
 *
 * @param graphrep [in/out] composant à libérer
 */
void dispose_graphrep(struct graphrep_t** graphrep);

/**
 * Récupère le viewport associé au composant.
 *
 * Pré-conditions : graphrep non NULL, viewport non NULL
 *
 * @param graphrep composant dont on veut le viewport
 * @param result [out] viewport résultat
 */
void get_viewport(struct graphrep_t* graphrep, viewport_t* result);

/**
 * Bouge la souris sur le composant (pour mettre à jour l'affichage de tooltip 
 * typiquement).
 *
 * Pré-conditions : graphrep non NULL
 *
 * @param graphrep composant à mettre à jour
 * @param pos position de la souris, usuellement obtenu via un event SDL
 */
void move_mouse(struct graphrep_t* graphrep, SDL_Point pos);

/**
 * Met en évidence un chemin dans le graphe, sous la forme de liste de noeud.
 *
 * Cette fonction affiche dans une couleur différente les noeuds du chemin, et les
 * arrêtes (ces dernières étant les couples (précédent(noeud), noeud) stockés dans le
 * chemin).
 *
 * Si path est NULL, la mise en évidence est annulée.
 *
 * Pré-conditions : graphrep != NULL
 *
 * @param graphrep composant à mettre à jour
 * @param path chemin à mettre en évidence (ou NULL)
 */
void highlight_path(struct graphrep_t* graphrep, liste_noeud_t* path);

/**
 * Change la couleur (d'arrière plan) du noeud donné avec la couleur donnée.
 *
 * Pré-conditions : graphrep != NULL
 *
 * @param graphrep composant à mettre à jour
 * @param node noeud dont on veut changer la couleur
 * @param color couleur du noeud
 */
void highlight_node(struct graphrep_t* graphrep, noeud_id_t node, SDL_Color color);

/**
 * Met en évidence l'arrête donnée (si elle existe). Il ne peut y avoir qu'une seule arrête
 * mise en évidence. Si l'arrête n'existe pas, aucune arrête n'est mise en évidence, ce
 * qui permet de retirer la mise en évidence au besoin.
 *
 * À noter que si une arrête est mise en évidence et appartient au chemin actuellement mis en
 * évidence, elle n'apparaît pas (priorité au chemin).
 *
 * Pré-conditions : graphrep != NULL
 *
 * @param graphrep composant à mettre à jour
 * @param source source de l'arrête
 * @param dest destination de l'arrête
 */
void highlight_edge(struct graphrep_t* graphrep, noeud_id_t source, noeud_id_t dest);

/**
 * Recalcul le rendu du graphe. Cette fonction est appelée par la fenêtre lors du
 * repaint, et doit donc être appelée dans le thread de rendu.
 *
 * @param window fenêtre sur laquelle est rendu le graphe
 * @param userdata données utilisateur transmise par le thread, un graphrep en théorie
 */
void graphrep_repaint(struct window_t* window, void* userdata);


#endif // GRAPHREP_H


