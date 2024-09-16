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
 * @file point.c
 * @brief Implantation du module point
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "point.h"
#include <stdlib.h>
#include <math.h>

point_t creer_point(double x, double y) {
    point_t p = { .x = x, .y = y };
    return p;
}

void copier_point(point_t* cible, point_t source) {
    if (cible != NULL) {
        cible->x = source.x;
        cible->y = source.y;
    }
}

double distance(point_t a, point_t b) {
    double x = a.x - b.x;
    double y = a.y - b.y;
    return sqrt(x * x + y * y);
}

bool egal(point_t a, point_t b, double precision) {
    return distance(a, b) < precision;
}



