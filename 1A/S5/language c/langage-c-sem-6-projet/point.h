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
 * @file point.h
 * @brief Module point qui définit les points cartésiens. On utilise point_t plutôt
 * que SDL_Point pour les points "réels" (par opposition aux points dans les écrans).
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef POINT_H
#define POINT_H

#include <stdbool.h>

/**
 * Le type `point_t` pour représenter des points cartésiens avec coordonnées réelles.
 */
struct point_t {
    /** Abscisse du point */
    double x,
    /** Ordonnée du point */
           y;
};

/** Typedef pour l'enregistrement `point_t` */
typedef struct point_t point_t;

/**
 * Crée un point (sur la pile) avec les coordonnée données.
 * @param x abscisse du point
 * @param y ordonnée du point
 * @return point créé (sur la pile)
 */
point_t creer_point(double x, double y);

/**
 * Copier un point.
 *
 * Post-conditions : si cible != NULL, cible->x == source.x, cible->y == source.y
 *
 * @param cible [out] point récepteur de la copie
 * @param source point à copier
 */
void copier_point(point_t* cible, point_t source);

/**
 * Distance (euclidienne) entre deux points.
 *
 * @param a premier point
 * @param b second point
 * @return distance entre a et b (racine carrée de la norme-2)
 */
double distance(point_t a, point_t b);

/**
 * Teste si deux points sont égaux (à précision près).
 * Ce test se base sur la distance.
 *
 * @param a premier point
 * @param b second point
 * @param precision seuil en-dessous duquel les points sont considérés comme égaux
 */
bool egal(point_t a, point_t b, double precision);


#endif // POINT_H


