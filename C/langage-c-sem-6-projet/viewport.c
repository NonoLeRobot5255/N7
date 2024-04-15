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
 * @file viewport.c 
 * @brief Implantation du module viewport
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "viewport.h"

void mkrect(rect_t* result, point_t bottomleft, double w, double h) {
    result->bottom = bottomleft.y;
    result->left   = bottomleft.x;
    result->top    = bottomleft.y + h;
    result->right  = bottomleft.x + w;
}

void mkrect_corners(rect_t* result, point_t bottomleft, point_t topright) {
    result->bottom = bottomleft.y;
    result->left   = bottomleft.x;
    result->top    = topright.y;
    result->right  = topright.x;
}

void mkrect_center(rect_t* result, point_t center, double w, double h) {
    result->bottom = center.y - h / 2.0; 
    result->left   = center.x - w / 2.0; 
    result->top    = center.y + h / 2.0; 
    result->right  = center.x + w / 2.0; 
}

void get_size(rect_t rect, double* width, double* height) {
    if (width != NULL) {
        *width = rect.right - rect.left;
    }
    if (height != NULL) {
        *height = rect.top - rect.bottom;
    }
}

point_t get_center(rect_t rect) {
    point_t result = {
        .x = (rect.left + rect.right ) / 2.0,
        .y = (rect.top  + rect.bottom) / 2.0
    };
    return result;
}

void scale_move_center(rect_t* rect, double scale, point_t center) {
    double width, height;
    get_size(*rect, &width, &height);
    mkrect_center(rect, center, width * scale, height * scale);
}

void translate_rect(rect_t* rect, double dx, double dy) {
    rect->bottom += dy;
    rect->left   += dx;
    rect->right  += dx;
    rect->top    += dy;
}

void viewport(viewport_t* result, SDL_Rect display, rect_t real) {
    double alphax = (real.right - real.left) / ((double) display.w);
    double alphay = (real.bottom - real.right) / ((double) display.h);
    double betax = real.left - alphax * ((double) display.x);
    double betay = real.top - alphay * ((double) display.y);
    result->scale_x = alphax;
    result->scale_y = alphay;
    result->off_x = betax;
    result->off_y = betay;
}

void viewport_unit_aspect(viewport_t* result, SDL_Rect display, rect_t real) {
    double deltax = real.right - real.left;
    double ratio = ((double) display.h) / ((double) display.w);
    double deltay = deltax * ratio;
    real.top = real.bottom + deltay;
    viewport(result, display, real);
}

void viewport_unit_fit(viewport_t* result, SDL_Rect display, rect_t real) {
    double width, height, ratio, dratio, scale;
    get_size(real, &width, &height);
    ratio = height / width;
    dratio = ((double) display.h) / ((double) display.w);

    if (ratio > dratio) { // On essaye de fit la hauteur
        scale = height / ((double) display.h);    
    } else { // On essaye de fit la largeur
        scale = width / ((double) display.w);
    }

    point_t rcenter = get_center(real);
    point_t dcenter;
    dcenter.x = ((double) display.x) + ((double) display.w) / 2.0;
    dcenter.y = ((double) display.y) + ((double) display.h) / 2.0;

    result->scale_x =   scale;
    result->scale_y = - scale; // Ne pas oublier d'inverser la direction verticale
    result->off_x = rcenter.x - scale * dcenter.x;
    result->off_y = rcenter.y + scale * dcenter.y;
}

void copy_viewport(viewport_t* result, viewport_t source) {
    result->scale_x = source.scale_x;
    result->scale_y = source.scale_y;
    result->off_x = source.off_x;
    result->off_y = source.off_y;
}

void from_display_point(viewport_t viewport, point_t* real, SDL_Point display) {
    real->x = viewport.scale_x * ((double) display.x) + viewport.off_x;
    real->y = viewport.scale_y * ((double) display.y) + viewport.off_y;
}

void from_real_point(viewport_t viewport, SDL_Point* display, point_t real) {
    display->x = (int) ((real.x - viewport.off_x) / viewport.scale_x);
    display->y = (int) ((real.y - viewport.off_y) / viewport.scale_y);
}

void from_display_vec(viewport_t viewport, point_t* real, SDL_Point display) {
    real->x = viewport.scale_x * ((double) display.x) + viewport.off_x;
    real->y = viewport.scale_y * ((double) display.y) + viewport.off_y;
}

void from_real_vec(viewport_t viewport, SDL_Point* display, point_t real) {
    display->x = (int) ((real.x - viewport.off_x) / viewport.scale_x);
    display->y = (int) ((real.y - viewport.off_y) / viewport.scale_y);
}

void from_display_rect(viewport_t viewport, rect_t* real, SDL_Rect display) {
    SDL_Point p_bl;
    p_bl.x = display.x;
    p_bl.y = display.y + display.h;
    SDL_Point p_tr;
    p_tr.x = display.x + display.w;
    p_tr.y = display.y;
    point_t r_bl;
    point_t r_tr;
    from_display_point(viewport, &r_bl, p_bl);
    from_display_point(viewport, &r_tr, p_tr);
    mkrect_corners(real, r_bl, r_tr);
}

void from_real_rect(viewport_t viewport, SDL_Rect* display, rect_t real) {
    SDL_Point p_bl;
    SDL_Point p_tr;
    point_t r_bl, r_tr;
    r_bl.x = real.left;
    r_bl.y = real.bottom;
    r_tr.x = real.right;
    r_tr.y = real.top;
    from_real_point(viewport, &p_bl, r_bl);
    from_real_point(viewport, &p_tr, r_tr);
    display->x = p_bl.x;
    display->w = (p_tr.x - p_bl.x);
    display->h = (p_bl.y - p_tr.y);
    display->y = p_bl.y - display->h;
}




