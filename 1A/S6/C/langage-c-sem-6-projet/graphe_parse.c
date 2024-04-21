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
 * @file graphe_parse.c
 * @brief Implantation du module `graphe_parse`.
 *
 * Le module utilise abondamment des variables statiques car c'est plus pratique
 * que de passer 10 arguments de fonction en fonction...
 *
 * Les variables sont ré-initialisées au début de `parser_graphe`, si bien qu'elle
 * sont reliées à cette méthode spécifiquement (il ne s'agit pas d'un état persistant
 * du module, à la fin de la fonction les variables ne servent plus à rien).
 *
 * @author G. Dupont
 * @version 1.0
 */
#define _GNU_SOURCE
#include "graphe_parse.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include "parse_util.h"

// On ajoute les noeuds dans un tableau petit à petit (pas de liste chaînée...)
// Du coup on a un tableau dont la taille augment dynamiquement ; TAILLE_BLOCK
// est alors la taille initiale (et l'incrément) du tableau dynamique.
#define TAILLE_BLOCK    10

/**
 * Type interne qui représente le mode du parseur : par encore entré dans une section
 * (`NO_SECTION`), dans la section `Noeuds` (`NODE_SECTION`) ou dans la section 
 * `Liens` (`EDGE_SECTION`).
 */
enum parser_mode {
    NO_SECTION, NODE_SECTION, EDGE_SECTION
};

/**
 * Un noeud en cours de parsing, avec un identifiant, un nom et une position.
 * Cet enregistrement permet de faire le lien entre nom et identifiant (puisque
 * le fichier ne manipule _que_ des identifiants).
 *
 * Dans la suite, on appellera ça des "noeuds parseur" (par opposition aux
 * "vrais" noeuds du graphe).
 */
struct parser_noeud {
    /** Identifiant du noeud */
    noeud_id_t nid;
    /** Nom du noeud */
    char* nom;
    /** Position du noeud */
    point_t pos;
};

/** Tableau des noeuds (parseur) courants */
static struct parser_noeud* noeuds_courants;
/** Taille allouée de `noeuds_courants` */
static size_t num_blocks_noeuds;
/** Nombre de noeuds parsés (inférieur ou égal à `num_blocks_noeuds`) */
static size_t num_noeuds;
/** Numéro de ligne actuel (pour l'erreur reporting) */
static int ligne_num;
/** Graphe en cours de création */
static struct graphe_t* graphe;
/** Booléen qui vaut vrai si le graphe a été initialisé */
static bool graphe_initialise;

/**
 * Parser un noeud depuis la ligne donnée, et en commençant par l'indice
 * donné.
 *
 * La fonction découpe la ligne au niveau du ':' ; tout ce qui est avant
 * excepté le '-' et les espaces préfixes devient le nom du noeud, et tout
 * ce qui est après est interprété comme un couple de nombre. Les caractères
 * après la parenthèse fermante du couple sont ignorés (et donnent lieu à un
 * warning).
 *
 * Le noeud créé par cette fonction est celui à l'indice dont la valeur est celle de
 * `num_noeuds` avant la fonction (puisque cette valeur augmente après).
 *
 * @param ligne ligne à parser
 * @param debut indice du début de la ligne à parser (généralement juste après 
 * le tiret sur la ligne)
 * @return vrai si le prasing s'est bien passé
 */
static bool parser_noeud(const char* ligne, size_t debut) {
    size_t id = debut;

    manger_espaces(ligne, &id);
    if (!parser_jusqua(ligne, &id, ':')) {
        fprintf(stderr, "Ligne %d: ligne mal formée, caractère ':' manquant.\n", ligne_num);
        return false;
    }

    // Extension du tableau de noeuds alloués (si nécessaire)
    if (num_noeuds >= num_blocks_noeuds * TAILLE_BLOCK) {
        num_blocks_noeuds++;
        struct parser_noeud* tmp = (struct parser_noeud*)realloc(noeuds_courants, 
                num_blocks_noeuds * TAILLE_BLOCK * sizeof(struct parser_noeud));

        if (tmp != NULL) {
            noeuds_courants = tmp;
        }
    }

    // Trim
    size_t fin = id - 1;
    while (est_espace(ligne[fin]) && fin > debut) { fin--; }

    // Nom du noeud
    noeuds_courants[num_noeuds].nom = (char*)malloc((fin - debut + 2) * sizeof(char));
    memcpy(noeuds_courants[num_noeuds].nom, ligne + debut, (fin - debut + 1) * sizeof(char));
    noeuds_courants[num_noeuds].nom[fin - debut + 1] = '\0';

    for (size_t i = 0; i < num_noeuds; i++) {
        if (strcmp(noeuds_courants[num_noeuds].nom, noeuds_courants[i].nom) == 0) {
            fprintf(stderr, "Ligne %d: le noeud %s a déjà été déclaré.\n", 
                ligne_num, noeuds_courants[num_noeuds].nom);
            return false;
        }
    }

    // Première coordonnée
    if (!parser_jusqua(ligne, &id, '(')) {
        fprintf(stderr, "Ligne %d: ligne mal formée, caractère '(' attendu.\n", ligne_num);
        return false;
    }
    
    id++;
    manger_espaces(ligne, &id);
    
    char* end;
    size_t ndebut = id, nfin;
    
    if (!parser_jusqua(ligne, &id, ',')) {
        fprintf(stderr, "Ligne %d: ligne mal formée, caractère ',' attendu.\n", ligne_num);
        return false;
    }

    nfin = id - 1;
    while (est_espace(ligne[nfin]) && nfin > ndebut) { nfin--; }
    noeuds_courants[num_noeuds].pos.x = strtof(ligne + ndebut, &end);

    if (end < ligne + nfin) {
        fprintf(stderr, "Ligne %d, colonnes %ld-%ld: nombre mal formé.\n", ligne_num,
                ndebut + 1, nfin + 1);
        fprintf(stderr, "   |%s", ligne);
        fputs("    ", stderr);
        for (size_t i = 0; i < ndebut; i++) { fputc(' ', stderr); }
        for (size_t i = ndebut; i < nfin; i++) { fputc('^', stderr); }
        fputc('\n', stderr);
        return false;
    }

    // Seconde coordonnée
    id++;
    manger_espaces(ligne, &id);
    ndebut = id;

    if (!parser_jusqua(ligne, &id, ')')) {
        fprintf(stderr, "Ligne %d: ligne mal formée, caractère ')' manquant.\n", ligne_num);
        return false;
    }

    nfin = id - 1;
    while (est_espace(ligne[nfin]) && nfin > ndebut) { nfin--; }
    noeuds_courants[num_noeuds].pos.y = strtof(ligne + ndebut, &end);

    if (end < ligne + nfin) {
        fprintf(stderr, "Ligne %d, colonnes %ld-%ld: nombre mal formé.\n", ligne_num,
                ndebut + 1, nfin + 1);
        fprintf(stderr, "   |%s", ligne);
        fputs("    ", stderr);
        for (size_t i = 0; i < ndebut; i++) { fputc(' ', stderr); }
        for (size_t i = ndebut; i < nfin; i++) { fputc('^', stderr); }
        fputc('\n', stderr);
        return false;
    }

    id++;
    bool erreur_affichee = false;
    while (ligne[id] != '\0') {
        id++;
        if (!erreur_affichee && (ligne[id] != '\0' && !est_espace(ligne[id]))) {
            fprintf(stderr, "Ligne %d, colonne %ld: attention, caractère(s) en trop sur la ligne (ignoré).\n",
                    ligne_num, id + 1);
            erreur_affichee = true;
        }
    }

    num_noeuds++;

    return true;
}

/**
 * Initialise le graphe avec les noeuds parseurs qui ont viennent de la seciton `Noeuds`.
 */
static void initialiser_graphe() {
    graphe = creer_graphe(num_noeuds);

    for (size_t i = 0; i < num_noeuds; i++) {
        noeuds_courants[i].nid = creer_noeud(graphe, noeuds_courants[i].pos, (void*) noeuds_courants[i].nom);
    }

    graphe_initialise = true;
}

/**
 * Trouve l'identifiant du noeud associé au nom donné, en comparant aussi
 * la taille à n.
 * @param nom nom du noeud à trouver
 * @param n taille attendue
 * @return identifiant du noeud ou @ref NO_ID si le noeud n'a pas été trouvé
 */
static noeud_id_t trouver_noeud_nom(const char* nom, size_t n) {
    noeud_id_t resultat = NO_ID;
    size_t i = 0;
    while (i < num_noeuds && resultat == NO_ID) {
        if (n == strlen(noeuds_courants[i].nom) && strncmp(noeuds_courants[i].nom, nom, n) == 0) {
            resultat = noeuds_courants[i].nid;
        }
        i++;
    }

    return resultat;
}

/**
 * Parser le lien décrit par la ligne de texte donné, en commençant par
 * l'indice "debut".
 *
 * La source du noeud est l'identifiant avant le "->" (modulo espaces préfixes et tiret
 * préliminaire) et la destination est tout ce qu'il y a après.
 *
 * @param ligne ligne à parser
 * @param debut indice de début à partir duquel parser
 * @return vrai si la ligne a pu être parsée (faux sinon
 */
static bool parser_lien(const char* ligne, size_t debut) {
    size_t id = debut;

    manger_espaces(ligne, &id);
    size_t ndebut = id;
    bool ok, isbidir = false;

    ok = parser_jusqua2(ligne, &id, '-', '>');

    if (!ok) {
        id = ndebut;
        ok = parser_jusqua2(ligne, &id, '-', '-');
        isbidir = ok;
    }

    if (!ok) {
        fprintf(stderr, "Ligne %d: caractères '->' ou '--' attendus.\n", ligne_num);
        return false;
    }

    size_t nfin = id - 1;
    while (est_espace(ligne[nfin]) && nfin > ndebut) { nfin--; }

    noeud_id_t source = trouver_noeud_nom(ligne + ndebut, nfin - ndebut + 1);

    if (source == NO_ID) {
        fprintf(stderr, "Ligne %d: noeud source ('%.*s') jamais déclaré.\n", 
                ligne_num, (int)(nfin - ndebut + 1), ligne + ndebut);
        return false;
    }

    id += 2;
    manger_espaces(ligne, &id);
    ndebut = id;
    nfin = strlen(ligne) - 1;
    while (est_espace(ligne[nfin]) && nfin > debut) { nfin--; }

    noeud_id_t cible = trouver_noeud_nom(ligne + ndebut, nfin - ndebut + 1);

    if (cible == NO_ID) {
        fprintf(stderr, "Ligne %d: noeud cible ('%.*s') jamais déclaré.\n", 
                ligne_num, (int)(nfin - ndebut + 1), ligne + ndebut);
        return false;
    }

    if (!ajouter_arrete(graphe, source, cible)) {
        fprintf(stderr, "Ligne %d: l'arrête existe déjà dans le graphe.\n", ligne_num);
        return false;
    }

    if (isbidir) {
        if (!ajouter_arrete(graphe, cible, source)) {
            fprintf(stderr, "Ligne %d: l'arrête existe déjà dans le graphe.\n", ligne_num);
            return false;
        }
    }

    return true;
}

struct graphe_t* parser_graphe(const char* filename) {
    graphe = NULL; 

    FILE* fichier = fopen(filename, "r");
    if (fichier == NULL) {
        fprintf(stderr, "Impossible d'ouvrir le fichier %s : (%d) %s\n",
                filename, errno, strerror(errno));
        perror("Impossible d'ouvrir le fichier:");
        return NULL;
    }

    bool ok = true;

    char* ligne = NULL;
    size_t taille = 0;
    int id;
    enum parser_mode mode = NO_SECTION;

    ligne_num = 0;
    noeuds_courants = (struct parser_noeud*)malloc(TAILLE_BLOCK * sizeof(struct parser_noeud));
    num_blocks_noeuds = 1;
    num_noeuds = 0;
    graphe_initialise = false;

    while (getline(&ligne, &taille, fichier) >= 0) {
        ligne_num++;
        id = 0;

        if (commence(ligne, "Noeuds\\>", ":", NULL) >= 0) {
            if (mode != NO_SECTION) {
                fprintf(stderr, "Ligne %d: début de section \"Noeuds\" invalide\n", ligne_num);
                ok = false;
            } else {
                mode = NODE_SECTION;
            }
        } else if (commence(ligne, "Liens\\>", ":", NULL) >= 0) {
            if (mode != NODE_SECTION) {
                fprintf(stderr, "Ligne %d: début de section \"Liens\" invalide.\n", ligne_num);
                ok = false;
            } else {
                initialiser_graphe();
                mode = EDGE_SECTION;
            }
        } else if ((id = commence(ligne, "-", NULL)) >= 0) {
            id++;
            if (mode == NODE_SECTION) {
                ok = ok && parser_noeud(ligne, (size_t) id);
            } else if (mode == EDGE_SECTION) {
                ok = ok && parser_lien(ligne, (size_t) id);
            } else {
                fprintf(stderr, "Ligne %d: déclaration de noeud ou d'arrête en dehors d'une section.\n", ligne_num);
                ok = false;
            }
        } else {
            size_t lid = 0;
            manger_espaces(ligne, &lid);
            if (lid < strlen(ligne)) {
                fprintf(stderr, "Ligne %d: ligne inattendue (ni un début de section, ni un élément dans une section).\n", ligne_num);
                ok = false;
            }
        }

    }

    // C'est la responsabilité de l'appelant de libérer la ligne
    free(ligne);
    ligne = NULL;

    fclose(fichier);

    if (!ok) {
        if (graphe_initialise) {
            liberer_graphe(&graphe, free);
        } else {
            fprintf(stderr, "Le graphe n'a pas plus être initialisé :(\n");
            graphe = NULL;
        }
    }

    struct graphe_t* resultat = graphe;
    graphe = NULL;
    free(noeuds_courants);
    noeuds_courants = NULL;
    return resultat;
}


