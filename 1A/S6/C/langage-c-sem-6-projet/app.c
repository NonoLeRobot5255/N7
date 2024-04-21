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
 * @file app.c 
 * @brief Implantation du module app
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "util.h"
#include "window.h"
#include "graphrep.h"
#include "app.h"

/**
 * Implémentation du type abstrait @ref app_t.
 *
 * Dans les grandes lignes, ce type ne fait que maintenir ensemble les composants
 * et la config de l'app.
 */
struct app_t {
    /** Fenêtre de l'application (dont thread de rendu) */
    struct window_t* window;

    /** Composant de représentation de graphe */
    struct graphrep_t* graphrep;

    /** Viewport (actuel) de l'application */
    viewport_t viewport;

    /** Tâche parallèle */
    SDL_Thread* thread;
};

/** 
 * Lance le pré-rendu des composants de l'app.
 * @param window fenêtre à pré-rendre
 * @param userdata donnée utilisateur donnée à la création du thread, qui contient l'app
 */
static void app_repaint(struct window_t* window, void* userdata) {
    struct app_t* app = (struct app_t*) userdata;
    graphrep_repaint(window, app->graphrep);
}

/** La couleur blanche (solide) */
static const SDL_Color WHITE = { .r = 0xFF, .g = 0xFF, .b = 0xFF, .a = 0xFF };

struct app_t* setup_app(int width, int height, struct graphe_t* graph) {
    // Allocation dynamique de l'"objet" app
    struct app_t* app = (struct app_t*)malloc(sizeof(struct app_t));

    SDL_Rect display, area;
    display.x = 0;
    display.y = 0;
    display.w = width;
    display.h = height;
    area = display;
    area.x += PADDING;
    area.y += PADDING;
    area.w -= 2 * PADDING;
    area.h -= 2 * PADDING;

    // On se contente d'appeler les "constructeurs" de chaque module
    app->window = create_window(width, height, "Dijkstra", app_repaint, app);
    app->graphrep = create_graphrep_with_vp(app->window, graph, area);
    get_viewport(app->graphrep, &(app->viewport));

    set_background_color(app->window, WHITE);

    app->thread = NULL;

    return app;
}

void launch_app(struct app_t* app) {
    TLog("<app> Starting app");
    // On démarre la fenêtre (= ouvrir la fenêtre et lancer le thread de rendu)
    start_window(app->window);
    // On rafraîchit l'affichage (pour avoir le repère graphique)
    refresh_app(app);
}

void refresh_app(struct app_t* app) {
    refresh_window(app->window);
}

void move_cross_app(struct app_t* app, int x, int y) {
    SDL_Point p;
    p.x = x;
    p.y = y;
    move_mouse(app->graphrep, p);
    refresh_app(app);
}

void terminate_app(struct app_t** app_ptr) {
    struct app_t* app = *app_ptr;
    TLog("<app> Stopping app");

    if (app->thread != NULL) {
        SDL_WaitThread(app->thread, NULL);
        app->thread = NULL;
    }

    // Attention l'ordre est important pour éviter que les fonctions utilisent
    // un pointeur partagé qui a été libéré
    dispose_graphrep(&app->graphrep);
    stop_window(&app->window);
    free(app);
    *app_ptr = NULL;
}

/**
 * Enregistrement à transmettre à task_fun_bundle, contient les paramètres 
 * de la tâche.
 */
struct __task_data_t {
    /** app parente du thread */
    struct app_t* app;
    /** fonction représentant la tâche à réaliser */
    task_fun_t task;
    /** fonction de traitement poste-tâche */
    post_task_fun_t post;
    /** données utilisateur à transmettre aux fonctions */
    void* userdata;
};

/**
 * Fonction appelée lors de la création de la tâche. Cette fonction
 * se contente d'appeler les fonctions empaquetées dans le task data
 * et données par l'utilisateur, en interprétant les codes d'erreur.
 *
 * C'est aussi cette fonction qui libère les data.
 *
 * @param userdata données user transmise au moment de la création du thread (les task data ici)
 * @return code d'erreur (de la tâche ou du traitement post-tâche)
 */
static int task_fun_bundle(void* userdata) {
    struct __task_data_t* data = (struct __task_data_t*) userdata;

    int ret = data->task(data->app, data->userdata);

    if (ret == 0 && data->post != NULL) {
        ret = data->post(data->app, data->userdata);
    }

    free(userdata);

    return ret;
}

void exec_task_app(struct app_t* app, task_fun_t task, post_task_fun_t post, void* userdata, bool detach) {
    if (app->thread != NULL) {
        SDL_WaitThread(app->thread, NULL);
        app->thread = NULL;
    }

    struct __task_data_t* data = (struct __task_data_t*)malloc(sizeof(struct __task_data_t));
    data->app = app;
    data->task = task;
    data->post = post;
    data->userdata = userdata;

    SDL_Thread* thread = SDL_CreateThread(task_fun_bundle, "thread-task", data);

    if (detach) {
        SDL_DetachThread(thread);
    } else {
        app->thread = thread;
    }
}

void highlight_path_app(struct app_t* app, liste_noeud_t* path) {
    highlight_path(app->graphrep, path);
    refresh_app(app);
}

void highlight_node_app(struct app_t* app, noeud_id_t node, SDL_Color color) {
    highlight_node(app->graphrep, node, color);
    refresh_app(app);
}

void highlight_edge_app(struct app_t* app, noeud_id_t source, noeud_id_t destination) {
    highlight_edge(app->graphrep, source, destination);
    refresh_app(app);
}

