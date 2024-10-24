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
 * @file graphe.c
 * @brief Implantation du module graphe
 *
 * @author G. Dupont
 * @version 1.0
 */
#define _GNU_SOURCE
#include "graphe.h"
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <math.h>

// On a besoin du standard C99 au minimum (pour certaines constantes notamment)
#if !defined(__STDC__) || (__STDC_VERSION__ < 199901L)
#error "Ce module doit être compilé avec le standard C99 ou plus récent."
#endif

// On a besoin de NAN et INFINITY pour les distances dans le graphe
#if !defined(NAN) || !defined(INFINITY)
#error "Le système cible ne semble pas supporter la norme IEEE 754, nécessaire pour la compilation de ce module."
#error "Veuillez changer de système ou contacter l'auteur des sources."
#endif

/**
 * Noeud d'un graphe.
 */
struct graphe_noeud {
    /** Identifiant du noeud (calculé à l'appel de @ref creer_noeud) */
    noeud_id_t id;
    /** Position cartésienne du noeud */
    point_t position;
    /** Donnée utilisateur du noeud */
    void* donnees;

    /** Nombre de voisins (directs) du noeud */
    size_t nombre_voisins;
    /** Tableau des voisins du noeud.
     * La taille réelle du tableau est égale au nombre de noeuds dans le graphe ;
     * normalement on a pas besoin de plus (!), mais si le graphe n'est pas fortement
     * connexe, ça fait pas mal d'espace gaspillé...
     * En échange, c'est rapide et pratique.
     */
    noeud_id_t* voisins;
};

/**
 * Implantation du type abstrait graphe_t
 */
struct graphe_t {
    /** Capacité max du graphe, donnée à la cration du graphe. */
    size_t nombre_noeuds_max;
    /** Nombre de noeuds dans le graphe (&le; @ref nombre_noeuds_max) */
    size_t nombre_noeuds;
    /** Tableau des pointeurs sur les noeuds du graphe (les noeuds sont alloués sur le tas) */
    struct graphe_noeud** noeuds;
};

/**
 * Crée un identifiant unique de noeud à partir du numéro du noeud.
 * La façon dont l'identifiant est créé est caché, mais il fait intervenir le temps
 * CPU en nanosecondes, donc la probabilité de collision à num égal est très faible
 * @param num numéro du noeud dans le graphe (numéro de la case dans le champ noeuds)
 * @return identifiant unique du noeud
 */
static noeud_id_t creer_id(size_t num) {
    struct timespec spec;
    clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &spec);
    noeud_id_t id = 
        ((unsigned long) ((spec.tv_nsec & 0xFFFFFFFF) << 32))
      | ((unsigned long) ((spec.tv_sec & 0x0000FFFF) << 16))
      | ((unsigned long) (num & 0xFFFF));
    return id;
}

/**
 * Récupère le numéro interne du noeud à partir de l'identifiant de celui-ci.
 * @param id identifiant du noeud
 * @return position du noeud dans le tableau noeuds du graphe
 */
static size_t get_num(noeud_id_t id) {
    return (size_t)(id & 0xFFFF);
}

/**
 * Helper qui vérifie si le noeud donné est valide (i.e. il existe dans le graphe et il ne
 * correspond pas à @ref NO_ID).
 * Si le noeud n'est pas valide, affiche un message en se servant des informations données.
 * Si le noeud est valide, met le numéro associé dans la variable getnum.
 * @param graphe graphe de travial
 * @param loc fonction appelante, pour renseigner l'utilisateur
 * @param id noeud sous forme d'identifiant
 * @param getnum [out] numéro interne du noeud (non-utilisé si NULL)
 * @return vrai ssi le noeud est valide
 */
static bool check_id(const struct graphe_t* graphe, const char* loc, noeud_id_t id, size_t* getnum) {
    size_t num = get_num(id);
    if (id == NO_ID) {
        fprintf(stderr, "Accès à un noeud invalide (id=NO_ID, fonction %s)\n", loc);
        return false;
    }
    if (num > graphe->nombre_noeuds) {
        fprintf(stderr, "Accès à un noeud hors du graphe (id=%016lx, fonction %s)\n", id, loc);
        return false;
    }

    if (getnum != NULL) {
        *getnum = num;
    }
    return true;
}

/**
 * Helper pour allouer un noeud avec l'identifiant donné.
 * Le noeud est créé sur le tas.
 * @param num numéro du noeud
 * @return noeud nouvellement alloué, dont l'identifiant est compatible avec num
 * (créé avec @ref creer_id)
 */
static struct graphe_noeud* allouer_noeud(size_t num) {
    struct graphe_noeud* noeud = (struct graphe_noeud*)malloc(sizeof(struct graphe_noeud));
    noeud->id = creer_id(num);
    return noeud;
}

/**
 * Helper pour allouer le graphe avec le nombre de noeuds donné.
 * @param nnoeuds nombre de noeuds
 * @return graphe nouvellement alloué, avec de la place pour nnoeuds noeuds et initialement
 * aucun noeud dedans.
 */
static struct graphe_t* allouer_graphe(size_t nnoeuds) {
    struct graphe_t* graphe = (struct graphe_t*)malloc(sizeof(struct graphe_t));
    graphe->nombre_noeuds_max = nnoeuds;
    graphe->nombre_noeuds = 0;
    graphe->noeuds = (struct graphe_noeud**)malloc(nnoeuds * sizeof(struct graphe_noeud));
    return graphe;
}

struct graphe_t* creer_graphe(size_t nombre_noeuds) {
    if (nombre_noeuds > 0xFFFF) {
        fputs("La taille demandée pour le graphe est trop importante\n", stderr);
        return NULL;
    }
    return allouer_graphe(nombre_noeuds);
}

noeud_id_t creer_noeud(struct graphe_t* graphe, point_t position, void* donnees) {
    size_t num = graphe->nombre_noeuds;

    if (num >= graphe->nombre_noeuds_max) {
        fputs("Il n'y a plus de place pour de nouveaux noeuds\n", stderr);
        return NO_ID;
    }

    graphe->noeuds[num] = allouer_noeud(num);
    graphe->noeuds[num]->position = position;
    graphe->noeuds[num]->donnees = donnees;
    graphe->noeuds[num]->nombre_voisins = 0;
    graphe->noeuds[num]->voisins = (noeud_id_t*)malloc(graphe->nombre_noeuds_max * sizeof(noeud_id_t));

    graphe->nombre_noeuds++;
    return graphe->noeuds[num]->id;
}

bool ajouter_arrete(struct graphe_t* graphe, noeud_id_t source, noeud_id_t destination) {
    size_t num_src, num_dst;

    if (!check_id(graphe, "creer_arrete", source, &num_src) || !check_id(graphe, "creer_arrete", destination, &num_dst)) {
        return false;
    }

    struct graphe_noeud* noeud_src = graphe->noeuds[num_src];

    size_t idv = 0;
    while (idv < noeud_src->nombre_voisins && noeud_src->voisins[idv] != destination) {
        idv++;
    }

    bool ajout = (idv >= noeud_src->nombre_voisins);
    noeud_src->voisins[idv] = destination;
    
    if (ajout) {
        noeud_src->nombre_voisins++;
    }

    return ajout;
}

void liberer_graphe(struct graphe_t** graphe, void (*liberer_donnees)(void*)) {
    for (size_t i = 0; i < (*graphe)->nombre_noeuds; i++) {
        if (liberer_donnees != NULL && (*graphe)->noeuds[i]->donnees != NULL) {
            liberer_donnees((*graphe)->noeuds[i]->donnees);
            (*graphe)->noeuds[i]->donnees = NULL;
        }
        free((*graphe)->noeuds[i]->voisins);
        free((*graphe)->noeuds[i]);
    }
    free((*graphe)->noeuds);
    free(*graphe);
    *graphe = NULL;
}

size_t nombre_noeuds(const struct graphe_t* graphe) {
    return graphe->nombre_noeuds;
}

void noeuds(const struct graphe_t* graphe, noeud_id_t* noeuds) {
    memcpy(noeuds, graphe->noeuds, graphe->nombre_noeuds * sizeof(noeud_id_t));
}

bool est_voisin(const struct graphe_t* graphe, noeud_id_t source, noeud_id_t destination) {
    size_t num_src;

    if (!check_id(graphe, "est_voisin", source, &num_src) || !check_id(graphe, "est_voisin", destination, NULL)) {
        return false;
    }

    struct graphe_noeud* noeud_src = graphe->noeuds[num_src];
    size_t idv = 0;

    while (idv < noeud_src->nombre_voisins && noeud_src->voisins[idv] != destination) {
        idv++;
    }

    return idv < noeud_src->nombre_voisins;
}

size_t nombre_voisins(const struct graphe_t* graphe, noeud_id_t noeud) {
    size_t num;
    if (!check_id(graphe, "nombre_voisins", noeud, &num)) {
        return 0;
    }

    return graphe->noeuds[num]->nombre_voisins;
}

void noeuds_voisins(const struct graphe_t* graphe, noeud_id_t noeud, noeud_id_t* voisins) {
    size_t num;
    if (!check_id(graphe, "noeuds_voisins", noeud, &num)) {
        return;
    }

    size_t nvois = graphe->noeuds[num]->nombre_voisins;
    memcpy(voisins, graphe->noeuds[num]->voisins, nvois * sizeof(noeud_id_t));
}

void* noeud_donnees(const struct graphe_t* graphe, noeud_id_t noeud) {
    size_t num;

    if (!check_id(graphe, "noeud_position", noeud, &num)) {
        return NULL;
    }

    return graphe->noeuds[num]->donnees;
}

point_t noeud_position(const struct graphe_t* graphe, noeud_id_t noeud) {
    size_t num;

    if (!check_id(graphe, "noeud_position", noeud, &num)) {
        point_t p = { .x = 0.f, .y = 0.f };
        return p;
    }

    return graphe->noeuds[num]->position;
}

float noeud_distance(const struct graphe_t* graphe, noeud_id_t noeuda, noeud_id_t noeudb) {
    size_t numa;
    if (!check_id(graphe, "distance", noeuda, &numa) || !check_id(graphe, "distance", noeudb, NULL)) {
        return NAN;
    }

    float retour = INFINITY;

    struct graphe_noeud* noeud_src = graphe->noeuds[numa];
    size_t idv = 0;
    bool continuer = true;

    while (idv < noeud_src->nombre_voisins && continuer) {
        if (noeud_src->voisins[idv] == noeudb) {
            continuer = false;
            size_t idb = get_num(noeud_src->voisins[idv]);
            retour = distance(noeud_src->position, graphe->noeuds[idb]->position);
        }
        idv++;
    }

    return retour;
}

noeud_id_t trouver_noeud(const struct graphe_t* graphe, noeud_predicat predicat, void* userdata) {
    struct noeud_info_t info;
    size_t i = 0;
    noeud_id_t resultat = NO_ID;

    while (resultat == NO_ID && i < graphe->nombre_noeuds) {
        info.id         = graphe->noeuds[i]->id;
        info.position   = graphe->noeuds[i]->position;
        info.noeud_data = graphe->noeuds[i]->donnees;

        if (predicat(info, userdata)) {
            resultat = info.id;
        }

        i++;
    }

    return resultat;
}

void pour_chaque_noeud(struct graphe_t* graphe, noeud_iterateur iterateur, void* userdata) {
    struct noeud_info_t info;
    for (size_t i = 0; i < graphe->nombre_noeuds; i++) {
        info.id         = graphe->noeuds[i]->id;
        info.position   = graphe->noeuds[i]->position;
        info.noeud_data = graphe->noeuds[i]->donnees;
        iterateur(info, userdata);
    }
}

void pour_chaque_arrete(struct graphe_t* graphe, arrete_iterateur iterateur, void* userdata) {
    struct arrete_info_t info;
    for (size_t i = 0; i < graphe->nombre_noeuds; i++) {
        info.id_source         = graphe->noeuds[i]->id;
        info.position_source   = graphe->noeuds[i]->position;
        info.noeud_data_source = graphe->noeuds[i]->donnees;
        for (size_t j = 0; j < graphe->noeuds[i]->nombre_voisins; j++) {
            size_t destn = get_num(graphe->noeuds[i]->voisins[j]);
            info.id_destination         = graphe->noeuds[destn]->id;
            info.position_destination   = graphe->noeuds[destn]->position;
            info.noeud_data_destination = graphe->noeuds[destn]->donnees;
            iterateur(info, userdata);
        }
    }
}

void exporter_dot(const struct graphe_t* graphe, FILE* sortie, void(*afficher_donnees)(FILE*,void*)) {
    time_t rawtime;
    struct tm* timeinfo;
    time(&rawtime);
    timeinfo = localtime(&rawtime);

    char* temps_str = asctime(timeinfo);
    temps_str[strlen(temps_str) - 1] = '\0';

    fprintf(sortie, "/* Graphe généré par exporter_dot - %s */\n", temps_str);
    fputs("digraph {\n", sortie);

    for (size_t i = 0; i < graphe->nombre_noeuds; i++) {
        struct graphe_noeud* noeud = graphe->noeuds[i];
        size_t num = get_num(noeud->id);

        if (afficher_donnees == NULL) {
            fprintf(sortie, "    N%lu[label=\"\\#%lu (%f,%f)\" tooltip=\"<%016lx>\"];\n",
                    num, num, noeud->position.x, noeud->position.y,
                    noeud->id);
        } else {
            fprintf(sortie, "    N%lu[label=\"\\#%lu (%f,%f)\" tooltip=\"<%016lx> (",
                    num, num, noeud->position.x, noeud->position.y,
                    noeud->id);
            afficher_donnees(sortie, noeud->donnees);
            fprintf(sortie, ")\"];\n");
        }
    }

    for (size_t i = 0; i < graphe->nombre_noeuds; i++) {
        struct graphe_noeud* noeud = graphe->noeuds[i];
        size_t numi = get_num(noeud->id);
        for (size_t j = 0; j < noeud->nombre_voisins; j++) {
            size_t numj = get_num(noeud->voisins[j]);
            fprintf(sortie, "    N%lu -> N%lu [label=\"%f\"];\n",
                    numi, numj, distance(noeud->position, graphe->noeuds[numj]->position));
        }
    }

    fputs("}\n", sortie);
}





