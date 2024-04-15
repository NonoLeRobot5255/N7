// This file is part of Dijkstra.
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
// dijkstra - Copyright (c) 2023 Guillaume Dupont
// Contact: <guillaume.dupont@toulouse-inp.fr>
/**
 * @file viewport.h 
 * @brief Module de gestion des viewport.
 *
 * Un viewport est fondamentalement une transformation qui permet de convertir
 * des coordonnées de l'écran en coordonnées du repère et inversément.
 *
 * Il varie avec les zoom et les translations.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef VIEWPORT_H
#define VIEWPORT_H

#include <SDL2/SDL_rect.h>
#include "point.h"

/**
 * Le type du viewport. Contient essentiellement deux transformations affines (pour les
 * deux axes).
 *
 * Attention, on ne devrait jamais manipuler directement les champs d'un viewport, au
 * risque de tout déformer !
 */
struct viewport_t {
    /** Mise à l'échelle horizontal */
    double scale_x;
    /** Décalage horizontal */
    double off_x;
    /** Mise à l'échelle vertical */
    double scale_y;
    /** Décalage vertical */
    double off_y;
};

/** typedef de `viewport_t` pour plus de facilité */
typedef struct viewport_t viewport_t;

/**
 * Un rectangle du plan cartésien est défini par les coordonnées rectilignes
 * de chacun de ses côtés (abscisse pour gauche et droite, ordonnée pour haut
 * et bas).
 * Ceci permet de rapidement deviner les quatre sommets du rectangle, de calculer
 * sa taille, etc.
 */
struct rect_t {
    /** Ordonnée du côté bas du rectangle */
    double bottom;
    /** Abscisse du côté gauche du rectangle */
    double left;
    /** Abscisse du côté droite du rectangle */
    double right;
    /** Ordonnée du côté haut du rectangle */
    double top;
};

/** typedef de `rect_t` pour plus de facilité */
typedef struct rect_t rect_t;

/**
 * Initialise un rectangle à l'aide de son coin inférieur gauche et de ses dimensions.
 * Le rectangle se développe de gauche à droite et de bas en haut.
 *
 * Pré-conditions: w et h positifs, result != NULL
 *
 * @param result [sortie] rectangle initialisé
 * @param bottomleft coordonnées du coin inférieur gauche
 * @param w largeur du rectangle
 * @param h hauteur du rectangle
 */
void mkrect(rect_t* result, point_t bottomleft, double w, double h);

/**
 * Initialise un rectangle à l'aide de ses deux coins (inférieur gauche et
 * supérieur droit).
 *
 * Pré-conditions: bottomleft.x < topright.x, bottomleft.y < topright.y
 *
 * @param result [sortie] rectangle initialisé
 * @param bottomleft coordonnées du coin inférieur gauche
 * @param topright coordonées du coin supérieur droit
 */
void mkrect_corners(rect_t* result, point_t bottomleft, point_t topright);

/**
 * Initialise un rectangle à partir de son centre et de ses dimensions.
 *
 * Pré-conditions: w et h positifs, result != NULL
 *
 * @param result [sortie] rectangle initialisé
 * @param center coordonnées du centre du rectangle
 * @param w largeur du rectangle
 * @param h hauteur du rectangle
 */
void mkrect_center(rect_t* result, point_t center, double w, double h);

/**
 * Récupère les dimensions (largeur, hauteur) du rectangle.
 * Les arguments autorisent NULL auquel cas la dimension n'est pas
 * récupérée.
 *
 * Post-conditions: si width != NULL alors *width est positif
 * De même avec height
 *
 * @param rect rectangle dont on veut les dimensions
 * @param width [sortie] largeur du rectangle
 * @param height [sortie] hauteur du rectangle
 */
void get_size(rect_t rect, double* width, double* height);

/**
 * Récupère le point au centre du rectangle donné.
 * @param rect rectangle
 * @return centre de rect
 */
point_t get_center(rect_t rect);

/**
 * Déplace et met à l'échelle (homothétiquement) un rectangle, de façon à
 * ce que son centre soit celui spécifié.
 *
 * Pré-conditions: rect != NULL
 * Post-conditions: largeur et hauteur du rectangle multipliés par |scale|
 *
 * @param rect [entrée,sortie] rectangle à modifier et résultat de la modification
 * @param scale facteur d'échelle
 * @param center nouveau centre du rectangle
 */
void scale_move_center(rect_t* rect, double scale, point_t center);

/**
 * Déplace le rectangle selon le vecteur donné.
 *
 * Pré-conditions: rect != NULL
 *
 * @param rect [entrée,sortie] rectangle à modifier et résultat de la modification
 * @param dx déplacement d'abscisse
 * @param dy déplacement d'ordonnée
 */
void translate_rect(rect_t* rect, double dx, double dy);

/**
 * Calcul un viewport à partir d'un rectangle d'affichage (des coordonnées sur la   
 * fenêtre) et d'un rectangle représentant le repère.
 *
 * Attention, le repère de la fenêtre en SDL est orienté de gauche à droite et de 
 * haut en bas, alors que le plan cartésien est orienté en sens direct, c'est-à-dire 
 * de gauche à droite et de bas en haut.
 * Le viewport résultant crée donc une inversion de l'axe Y !
 *
 * Pré-conditions: result != NULL, display bien construit (largeur et hauteur
 * positives)
 *
 * @param result [sortie] viewport résultant
 * @param display rectangle qui représente la fenêtre
 * @param real rectangle du plan cartésien réel qui représente le repère
 */
void viewport(viewport_t* result, SDL_Rect display, rect_t real);

/**
 * Calcul un viewport à partir d'un rectangle d'affichage (des coordonnées de la
 * fenêtre) et d'un rectangle représentant le repère, en s'éforcant de maintenir
 * le ratio de la fenêtre dans le repère.
 *
 * La largeur du repère est privilégiée.
 *
 * Pré-conditions: result != NULL, display et real bien construits (largeur et 
 * hauteur positives)
 * Post-conditions: display.w / display.h == width(real) / height(real) et
 * width(real) correspond à display.w par le viewport
 *
 * @param result [sortie] viewport résultant
 * @param display rectangle qui représente la fenêtre
 * @param real rectangle qui représente le repère
 */
void viewport_unit_aspect(viewport_t* result, SDL_Rect display, rect_t real);

/**
 * Calcul un viewport à partir d'un rectangle d'affichage et d'un rectangle
 * représentant le repère, en s'éforçant de maintenir le ratio du repère dans
 * la fenêtre et tel que tout le repère apparaisse dedans.
 *
 * Pré-conditions: result != NULL, display et real bien construits (largeur et 
 * hauteur positives)
 * Post-conditions: image de width(real) < display.w, image de 
 * height(real) < display.h, image de width(real)/height(real) == width(real)/height(real)
 *
 * @param result [sortie] viewport résultant
 * @param display rectangle qui représente la fenêtre
 * @param real rectangle qui représente le repère
 */
void viewport_unit_fit(viewport_t* result, SDL_Rect display, rect_t real);

/**
 * Copie un viewport dans une autre variable.
 *
 * Pré-conditions: result != NULL
 *
 * @param result [sortie] viewport résultant
 * @param source viewport à copier
 */
void copy_viewport(viewport_t* result, viewport_t source);

/**
 * Transforme une coordonnée fenêtre en coordonnée réelle en utilisant le viewport
 * donné. Permet, par exemple, de transformer la position de la souris en coordonnées
 * dans le repère.
 *
 * Pré-conditions: real != NULL
 *
 * @param viewport viewport pour la transformation
 * @param real [sortie] point réel résultant
 * @param display point sur la fenêtre
 */
void from_display_point(viewport_t viewport, point_t* real, SDL_Point display);

/**
 * Transforme une coordonnée réelle du repère cartésien en coordonnée de la fenêtre 
 * en utilisant le viewport donné.
 *
 * Pré-conditions: display != NULL
 *
 * @param viewport viewport pour la transformation
 * @param display [sortie] point sur la fenêtre calculé
 * @param real point du repère
 */
void from_real_point(viewport_t viewport, SDL_Point* display, point_t real);

/**
 * Transforme un vecteur de la fenêtre (sous forme d'un point) en vecteur réel du plan
 * cartésien en utilisant le viewport. Permet, par exemple, de transformer un déplacement en
 * pixels en déplacement dans le repère pour en faire la translation.
 *
 * Pré-conditions: real != NULL
 *
 * @param viewport viewport pour la transformation
 * @param real [sortie] vecteur résultant
 * @param display vecteur dans la fenêtre, sous forme de point
 */
void from_display_vec(viewport_t viewport, point_t* real, SDL_Point display);

/**
 * Transforme un vecteur réel du repère cartésien en vecteur de la fenêtre (sous forme
 * de point).
 *
 * Pré-conditions: display != NULL
 *
 * @param viewport viewport pour la transformation
 * @param display [sortie] vecteur résultant
 * @param real vecteur dans la fenêtre
 */
void from_real_vec(viewport_t viewport, SDL_Point* display, point_t real);

/**
 * Transforme un rectangle de la fenêtre en rectangle du plan cartésien réel. Permet, par
 * exemple, de convertire une zone de la fenêtre en zone du repère pour faire le rendu.
 *
 * Pré-conditions: real != NULL, display bien formé (dimensions positives)
 *
 * @param viewport viewport pour la transformation
 * @param real [sortie] rectangle réel résultant
 * @param display rectangle de la fenêtre
 */
void from_display_rect(viewport_t viewport, rect_t* real, SDL_Rect display);

/**
 * Transforme un rectangle du plan cartrésien réel en rectangle de la fenêtre.
 *
 * Pré-conditions: display != NULL, real bien formé (points correctement placés)
 *
 * @param viewport viewport pour la transformation
 * @param display [sortie] rectangle de la fenêtre
 * @param real rectangle réel
 */
void from_real_rect(viewport_t viewport, SDL_Rect* display, rect_t real);


#endif // VIEWPORT_H


