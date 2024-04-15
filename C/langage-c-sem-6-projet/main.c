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
 * @file main.c
 * @brief Programme principal
 *
 * @author G. Dupont
 * @version 1.0
 */
#include <stdlib.h>
#include <stdio.h>
#include <SDL2/SDL_ttf.h>
#include <SDL2/SDL.h>
#ifdef _DEBUG // En mode debug on affiche le PID (pour kill plus facilement)
#include <unistd.h>
#endif // _DEBUG
#include <time.h>
#include <string.h>
#include "util.h"
#include "graphe.h"
#include "graphe_parse.h"
#include "app.h"
#include "dijkstra.h"
#ifdef AVEC_ANIMATION
#include "dijkstra_event.h"
#endif

/**
 * Prédicat pour rechercher un noeud par son nom (utilisé pour déterminer
 * l'identifiant de la source et de la destination).
 * @param info information sur le noeud (passé par l'itérateur)
 * @param userdata données passées à l'itérateur, contient le nom à trouver
 * @return vrai ssi le nom donné correspond au nom du noeud
 */
static bool with_name(struct noeud_info_t info, void* userdata) {
    return strcmp((char*) info.noeud_data, (char*) userdata) == 0;
}

#ifdef AVEC_ANIMATION
static const SDL_Color LIGHT_BLUE  = { .r = 0xC0, .g = 0xC0, .b = 0xFF, .a = 0xFF };
static const SDL_Color LIGHT_GREEN = { .r = 0xC0, .g = 0xFF, .b = 0xC0, .a = 0xFF };
static const SDL_Color LIGHT_RED   = { .r = 0xFF, .g = 0xC0, .b = 0xC0, .a = 0xFF };

static void highlight_visiting(noeud_id_t id, void* userdata) {
    struct app_t* app = (struct app_t*)userdata;
    highlight_node_app(app, id, LIGHT_BLUE);
    SDL_Delay(200);
}

static void highlight_marking(noeud_id_t id, void* userdata) {
    struct app_t* app = (struct app_t*)userdata;
    highlight_node_app(app, id, LIGHT_RED);
    SDL_Delay(200);
}

static void highlight_visited(noeud_id_t id, void* userdata) {
    struct app_t* app = (struct app_t*)userdata;
    highlight_node_app(app, id, LIGHT_GREEN);
    highlight_edge_app(app, NO_ID, NO_ID);
    SDL_Delay(200);
}

static void highlight_exploring(noeud_id_t src, noeud_id_t dst, void* userdata) {
    struct app_t* app = (struct app_t*)userdata;
    highlight_edge_app(app, src, dst);
    SDL_Delay(200);
}

static void highlight_path_build(liste_noeud_t* chemin, void* userdata) {
    struct app_t* app = (struct app_t*)userdata;
    highlight_path_app(app, chemin);
    SDL_Delay(200);
}
#endif

/**
 * Type qui représente la configuration de l'algo, à utiliser lorsqu'on donne
 * la conf à la tâche
 */
struct dijkstra_conf_t {
    /** graphe sur lequel effectuer l'algo */
    struct graphe_t* graphe;
    /** origine du chemin */
    noeud_id_t source, 
    /** destination du chemin */
               destination;

    /** chemin calculé par l'algo */
    liste_noeud_t* chemin;
    /** distance minimale calculée par l'algo */
    float resultat;
    /** temps de calcul */
    double temps;
};

/**
 * Réalise l'algorithme de dijkstra (à appeler avec le lanceur de tâche de l'app).
 * @param userdata données passé à la tâche, un @ref dijkstra_conf_t normalement
 * @return 0 si pas de problème
 */
static int perform_dijkstra(struct app_t* app, void* userdata) {
    struct dijkstra_conf_t* conf = (struct dijkstra_conf_t*)userdata;

    if (conf->chemin != NULL) {
        detruire_liste(&(conf->chemin));
    }

#ifndef AVEC_ANIMATION
    (void) app;
#endif

#ifdef AVEC_ANIMATION
    struct dijkstra_event_t callback;
    callback.on_visiting = highlight_visiting;
    callback.on_visited = highlight_visited;
    callback.on_marking = highlight_marking;
    callback.on_exploring = highlight_exploring;
    callback.on_path_build = highlight_path_build;
#endif

    clock_t begin, end;
    printf("Début du calcul du chemin le plus court...\n");
    begin = clock();
    conf->resultat = dijkstra(
            conf->graphe, 
            conf->source, conf->destination, 
            &(conf->chemin)
#ifdef AVEC_ANIMATION
            , callback, app
#endif
        );
    end = clock();

    conf->temps = ((double)(end - begin) / CLOCKS_PER_SEC);

    return 0;
}

/***
 * Réalise le post-traitement de l'algorithme (donc principalement montrer le chemin
 * et afficher distance minimale et temps de calcul).
 * @param app application dans laquelle rendre le chemin
 * @param userdata donnée passées à la création de tâche (un @ref dijkstra_conf_t normalement)
 * @return 0 si pas de problème
 */
static int show_chemin(struct app_t* app, void* userdata) {
    struct dijkstra_conf_t* conf = (struct dijkstra_conf_t*)userdata;
    highlight_path_app(app, conf->chemin);
    printf("Distance minimale : %f\n", conf->resultat);
    printf("Temps de calcul : %lf ms\n", conf->temps * 1.0e3);
    return 0;
}

/**
 * Le programme principal. Configure l'application, affiche la fenêtre et gère
 * les événements (clavier, souris...).
 * @param argc nombre d'arguments de la ligne de commande
 * @param argv arguments de la ligne de commande
 */
int main(int argc, char* argv[]) {
    // On affiche le PID
    MLog("pid=%d\n", getpid());

    if (argc < 4) {
        fputs("Erreur : le programme attend un ficher contenant la description d'un graphe, un noeud source et un neoud destination\n", stderr);
        exit(-1);
    }

    struct graphe_t* graphe = parser_graphe(argv[1]);

    if (graphe == NULL) {
        fputs("Le programme a été interrompu pour cause de problèmes dans le fichier passé en paramètre.\n", stderr);
        exit(-1);
    }

    noeud_id_t source, destination;
    source = trouver_noeud(graphe, with_name, argv[2]);
    destination = trouver_noeud(graphe, with_name, argv[3]);

    if (source == NO_ID || destination == NO_ID) {
        if (source == NO_ID) {
            fprintf(stderr, "Le noeud de source demandé (%s) n'existe pas dans le graphe.\n", argv[2]);
        }
        if (destination == NO_ID) {
            fprintf(stderr, "Le noeud de destination demandé (%s) n'existe pas dans le graphe.\n", argv[3]);
        }
        exit(-1);
    }


    /************** Lancement du programme **************/
    // Activation de la librairie graphique
    SDL_Init(SDL_INIT_VIDEO);
    TTF_Init();

    // Création de l'application
    int width = 1280;
    int height = 960;
    struct app_t* app = setup_app(width, height, graphe);

    // Lancement
    launch_app(app);

    /************** Tâche parallèle : calcul de plus cours chemin **************/
    struct dijkstra_conf_t conf;
    conf.graphe = graphe;
    conf.source = source;
    conf.destination = destination;
    conf.chemin = NULL;
    exec_task_app(app, perform_dijkstra, show_chemin, &conf, true);

    /************** Boucle principale : gestion des événements **************/
    SDL_Event event;
    bool quit = false;

    while (!quit) { // Tant que pas quitté
        // On attend un événement
        SDL_WaitEvent(&event);

        if (event.type == SDL_QUIT || (event.type == SDL_KEYDOWN && (event.key.keysym.sym == SDLK_q || event.key.keysym.sym == SDLK_ESCAPE))) { // croix/boutin escape/boutin Q => quitter
            quit = true;
        } else if (event.type == SDL_MOUSEMOTION) { // la souris bouge => mise à jour de la croix/curseur
            move_cross_app(app, event.motion.x, event.motion.y);
        } else if (event.type == SDL_MOUSEBUTTONDOWN) { // click => zoom/dé-zoom
            // NOP
        } else if (event.type == SDL_KEYDOWN) { 
            // NOP
        }
    }

    /************** Fin du programme et nettoyage **************/
    terminate_app(&app);

    if (conf.chemin != NULL) {
        free(conf.chemin);
    }

    MLog("Terminate TTF");
    TTF_Quit();

    MLog("Terminate SDL");
    SDL_Quit();

    MLog("End");
    return 0;
}



