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
 * @file graphrep.c
 * @brief Implantation du module graphrep
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "graphrep.h"
#include <stdbool.h>
#include <math.h>
#include "util.h"
#include <SDL2/SDL_mutex.h>
#include <SDL2/SDL_thread.h>

/** Met à jour la valeur de acc avec v si cette valeur est inférieure */
#define ACCMIN(acc, v)  if (acc > v) { acc = v; }
/** Met à jour la valeur de acc avec v si cette valeur est supérieure */
#define ACCMAX(acc, v)  if (acc < v) { acc = v; }

/**
 * Une liste de polices d'écriture à charger pour afficher le texte, par ordre
 * de préférence.
 *
 * Le principe est de les tester une par une jusqu'à ce qu'une d'entre elles marche...
 *
 * Si ça n'arrive pas ça risque de mal se passer (le code n'est pas très robuste de
 * ce côté là :| )
 */
static const char* PossibleFonts[] = { // Toutes ces font sont monospace/sans serif
    "TlwgMono.ttf",
    "/usr/share/fonts/truetype/tlwg/TlwgMono.ttf",
    "OpenSans-Regular.ttf",
    "/usr/share/fonts/truetype/open-sans/OpenSans-Regular.ttf",
    "DejaVuSansMono.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf",
    "DejaVuSans.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    NULL // dernière case = NULL pour indiquer la fin du tableau lorsqu'on le parcours
};

/**
 * Fonction auxiliaire qui charge la première police d'écriture de la liste de
 * suggestion, avec la taille donnée.
 *
 * @param ptsize taille de la police (en pt)
 * @return police nouvellement chargée, ou NULL si aucune des polices de @ref PossibleFonts n'a 
 *      pu être chargée
 */
static font_id_t find_font(struct window_t* window, int ptsize) {
    font_id_t result = -1;
    int i = 0;
    while (result < 0 && PossibleFonts[i] != NULL) {
        result = load_font(window, PossibleFonts[i], ptsize);
        i++;
    }
    MLog("Loaded font %s (internal ID=%d)", PossibleFonts[i], result);
    return result;
}

/** Type interne qui représente le style spécifique d'un noeud */
struct node_style_t {
    /** Couleur du noeud */
    SDL_Color color;
    /** Identifiant du noeud */
    noeud_id_t node;
};

/**
 * Composant de représentation du graphe.
 */
struct graphrep_t {
    /** Viewport du composant, pour faire correspondre les coordonnées des noeuds
     * avec celles de l'écran */
    viewport_t viewport;
    /** Zone de rendu du composant */
    SDL_Rect area;
    /** Graphe à représenter */
    struct graphe_t* graph;
    /** Chemin à mettre en évidence */
    liste_noeud_t* path;
    /** Couleur d'arrière-plan pour certains noeuds */
    struct node_style_t* node_styles;
    /** Origine de l'arrête à mettre en valeur */
    noeud_id_t hedge_origin,
    /** Destination de l'arrête à mettre en valeur */
               hedge_dest;

    /** Police de caractères pour les noeuds */
    font_id_t node_font;
    /** Police de caractères pour les tooltip */
    font_id_t tooltip_font;

    /** Coordonnées de la souris */
    SDL_Point mouse;

    /** Mutex en interne pour le partage entre threads */
    SDL_mutex* mutex;
};

struct graphrep_t* create_graphrep(struct window_t* window, struct graphe_t* graph, SDL_Rect area, viewport_t viewport) {
    struct graphrep_t* result = (struct graphrep_t*)malloc(sizeof(struct graphrep_t));
    result->graph = graph;
    copy_viewport(&(result->viewport), viewport);
    result->area.x = area.x;
    result->area.y = area.y;
    result->area.w = area.w;
    result->area.h = area.h;
    result->node_font = find_font(window, 12);
    result->tooltip_font = find_font(window, 10);
    result->path = NULL;
    result->node_styles = (struct node_style_t*)calloc(nombre_noeuds(graph), sizeof(struct node_style_t));
    result->hedge_origin = NO_ID;
    result->hedge_dest = NO_ID;
    result->mouse.x = -1;
    result->mouse.y = -1;
    result->mutex = SDL_CreateMutex();
    return result;
}

/** Type interne pour le résultat du min-max */
struct minmax_t {
    /** Vaut faux si l'enregistrement n'a pas encore été initialisé. */
    bool init;
    /** Minimum pour les coordonnées */
    point_t p_min;
    /** Maximum pour les coordonnées */
    point_t p_max;
};

/**
 * Calcul les coordonnées minimum et maximum pour représenter le graphe.
 * Cette fonction est appelée par @ref pour_chaque_noeud.
 *
 * @param info informations sur le noeud
 * @param udata données utilisateurs transmises par `pour_chaque_noeud`, normalement
 * un `minmax_t`.
 */
static void calc_minmax(struct noeud_info_t info, void* udata) {
    struct minmax_t* accum = (struct minmax_t*) udata;
    if (accum->init) {
        ACCMIN(accum->p_min.x, info.position.x);
        ACCMIN(accum->p_min.y, info.position.y);
        ACCMAX(accum->p_max.x, info.position.x);
        ACCMAX(accum->p_max.y, info.position.y);
    } else {
        accum->init = true;
        accum->p_min.x = info.position.x;
        accum->p_min.y = info.position.y;
        accum->p_max.x = info.position.x;
        accum->p_max.y = info.position.y;
    }

}

struct graphrep_t* create_graphrep_with_vp(struct window_t* window, struct graphe_t* graph, SDL_Rect area) {
    struct minmax_t result;
    result.init = false;
    pour_chaque_noeud(graph, calc_minmax, &result);

    rect_t vparea;
    mkrect_corners(&vparea, result.p_min, result.p_max);

    viewport_t viewport;
    viewport_unit_fit(&viewport, area, vparea);
    return create_graphrep(window, graph, area, viewport);
}

void dispose_graphrep(struct graphrep_t** graphrep){
    SDL_DestroyMutex((*graphrep)->mutex);
    free((*graphrep)->node_styles);
    free(*graphrep);
    *graphrep = NULL;
}

void get_viewport(struct graphrep_t* graphrep, viewport_t* result) {
    copy_viewport(result, graphrep->viewport);
}

void move_mouse(struct graphrep_t* graphrep, SDL_Point pos) {
    SDL_LockMutex(graphrep->mutex);
    graphrep->mouse.x = pos.x;
    graphrep->mouse.y = pos.y;
    SDL_UnlockMutex(graphrep->mutex);
}

void highlight_path(struct graphrep_t* graphrep, liste_noeud_t* path) {
    SDL_LockMutex(graphrep->mutex);
    graphrep->path = path;
    SDL_UnlockMutex(graphrep->mutex);
}

void highlight_node(struct graphrep_t* graphrep, noeud_id_t node, SDL_Color color) {
    SDL_LockMutex(graphrep->mutex);
    size_t nnoeuds = nombre_noeuds(graphrep->graph), i = 0;
    while (i < nnoeuds && graphrep->node_styles[i].node != NO_ID && graphrep->node_styles[i].node != node) {
        i++;
    }
    if (i < nnoeuds) {
        graphrep->node_styles[i].node = node;
        graphrep->node_styles[i].color = color;
    }
    SDL_UnlockMutex(graphrep->mutex);
}

void highlight_edge(struct graphrep_t* graphrep, noeud_id_t source, noeud_id_t dest) {
    SDL_LockMutex(graphrep->mutex);
    graphrep->hedge_origin = source;
    graphrep->hedge_dest = dest;
    SDL_UnlockMutex(graphrep->mutex);
}

/** Donnée pour le dessin, transmise par le thread de rendu */
struct draw_data_t {
    /** Composant de représentation du graphe. */
    struct graphrep_t* graphrep;
    /** Fenêtre à laquelle appartient le composant */
    struct window_t* window;
};

/** Couleur noir */
static const SDL_Color BLACK = { .r = 0, .g = 0, .b = 0, .a = 0xFF };
/** Couleur gris */
static const SDL_Color GRAY = { .r = 0xA0, .g = 0xA0, .b = 0xA0, .a = 0xFF };
/** Couleur rouge */
static const SDL_Color RED = { .r = 0xC0, .g = 0x00, .b = 0x00, .a = 0xFF };
/** Couleur transparent */
static const SDL_Color TRANSPARENT = { .r = 0, .g = 0, .b = 0, .a = 0 };
/** Couleur blanc */
static const SDL_Color WHITE = { .r = 0xFF, .g = 0xFF, .b = 0xFF, .a = 0xFF };
/** Couleur bleu */
static const SDL_Color BLUE = { .r = 0x40, .g = 0x40, .b = 0xD0, .a = 0xFF };

static struct node_style_t get_node_style(const struct graphrep_t* graphrep, noeud_id_t id) {
    size_t nnoeuds = nombre_noeuds(graphrep->graph);
    size_t i = 0;
    while (i < nnoeuds && graphrep->node_styles[i].node != NO_ID && graphrep->node_styles[i].node != id) {
        i++;
    }

    if (i < nnoeuds && graphrep->node_styles[i].node == id) {
        return graphrep->node_styles[i];
    } else {
        struct node_style_t style = { .color = TRANSPARENT, .node = NO_ID };
        return style;
    }
}

/**
 * Dessiner un noeud. Cette fonction est appelée par @ref pour_chaque_noeud depuis
 * la fonction appelée par la fenêtre (donc dans le thread de rendu).
 *
 * @param info informations du noeud
 * @param userdata données utilisateur, normalement un draw_data_t
 */
static void draw_node(struct noeud_info_t info, void* userdata) {
    struct draw_data_t* data = (struct draw_data_t*)userdata;

    SDL_Point center;
    from_real_point(data->graphrep->viewport, &center, info.position);

    // Déterminer si la souris survole le noeud
    float m2c_dist = NORM(
            (float)(center.x - data->graphrep->mouse.x),
            (float)(center.y - data->graphrep->mouse.y));
    bool hovered = m2c_dist < TOOLTIP_THRESH;

    // Text
    SDL_Color color;;

    if (data->graphrep->path != NULL && 
            contient_noeud_liste(data->graphrep->path,
                info.id)) {
        color = RED;
    } else {
        color = BLACK;
    }

    if (hovered) {
        color.a = 0xB0;
    }

    struct node_style_t nodestyle = get_node_style(data->graphrep, info.id);

    //render_circle(data->window, center.x, center.y, NODE_SIZE, color);
    render_text(data->window, (char*) info.noeud_data, data->graphrep->node_font, center.x, center.y,
            HALIGN_CENTER | VALIGN_MIDDLE, color, nodestyle.color);

    // Dessiner tooltip
    if (hovered) {
        char tooltip[256];
        sprintf(tooltip, "(%g,%g)", info.position.x, info.position.y);
        render_text(data->window, tooltip, data->graphrep->tooltip_font,
                data->graphrep->mouse.x, data->graphrep->mouse.y,
                HALIGN_LEFT | VALIGN_TOP, BLACK, WHITE);
    }
}

/**
 * Dessiner un arc. Cette fonction est appelée par @ref pour_chaque_arrete depuis
 * la fonction appelée par la fenêtre de rendu (donc dans le thread de rendu).
 *
 * @param info information de l'arrête
 * @param userdata données utilisateur un draw_data_t normalement
 */
static void draw_edge(struct arrete_info_t info, void* userdata) {
    struct draw_data_t* data = (struct draw_data_t*)userdata;

    SDL_Point src, dst;
    from_real_point(data->graphrep->viewport, &src, info.position_source);
    from_real_point(data->graphrep->viewport, &dst, info.position_destination);

    //render_line_thick(data->window, src.x, src.y, dst.x, dst.y, EDGE_WIDTH, GRAY);
    //const int skip = NODE_SIZE;
    //const float length = NORM(dst.x - src.x, dst.y - src.y);
    SDL_Color color;

    if (data->graphrep->path != NULL && 
            contient_arrete_liste(data->graphrep->path,
                info.id_source,
                info.id_destination)) {
        color = RED;
    } else if (info.id_source == data->graphrep->hedge_origin &&
               info.id_destination == data->graphrep->hedge_dest) {
        color = BLUE;
    } else {
        color = GRAY;
    }

    render_arrow_curved(data->window, 
            src.x, src.y, dst.x, dst.y, 
            8.0, 0.4, 25.0, 
            NODE_SIZE + NODE_SKIP, NODE_SIZE + NODE_SKIP, 
            color);
}

void graphrep_repaint(struct window_t* window, void* userdata) {
    if (userdata == NULL) {
        return;
    }

    struct graphrep_t* graphrep = (struct graphrep_t*) userdata;
    struct draw_data_t data;
    data.graphrep = graphrep;
    data.window = window;

    SDL_LockMutex(graphrep->mutex);
    pour_chaque_arrete(graphrep->graph, draw_edge, &data);
    pour_chaque_noeud(graphrep->graph, draw_node, &data);
    SDL_UnlockMutex(graphrep->mutex);
}




