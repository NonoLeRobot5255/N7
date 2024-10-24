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
 * @file test_dijkstra.c
 * @brief Tests unitaires pour l'algorithme de dijkstra
 *
 * @author G. Dupont
 * @version 1.0
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdbool.h>
#include <stdarg.h>
#include "tests.h"
#include "point.h"
#include "graphe.h"
#include "liste_noeud.h"
#include "dijkstra.h"

#define PRECISION   1e-4

/**
 * check_chemin - Fonction type ASSERT custom pour vérifier qu'un chemin se compose bien des 
 * noeuds donnés.
 *
 * Les noeuds donnés sont sous la forme d'une liste d'arguments (variadique) où chaque argument
 * est un identifiant de noeud, et terminant par NO_ID.
 *
 * La fonction vérifie que chaque noeud est bien dans la liste, et que les successions de noeuds
 * correspondent bien à la configuration (précédent(x), x) dans la liste. Pour le premier noeud,
 * on vérifie que le précédent est NO_ID.
 *
 * Si le chemin ne correspond pas, échoue le test actuel.
 *
 * @param graphe graphe dans lequel le chemin doit évoluer
 * @param chemin chemin à tester
 * @params liste des noeuds se terminant par NO_ID
 *
 */
static void ASSERT_FUN(check_chemin, const struct graphe_t* graphe, const liste_noeud_t* chemin, ...) {
    va_list attendus;
    va_start(attendus, chemin);
    noeud_id_t attendu, precedent;
    bool premiertour = true;
    while ((attendu = va_arg(attendus, noeud_id_t)) != NO_ID) {
        if (!contient_noeud_liste(chemin, attendu)) {
            FAILF("Le chemin ne contient pas le noeud <<%s>>\n", 
                    (char*) noeud_donnees(graphe, attendu));
        }
        if (premiertour) {
            if (precedent_noeud_liste(chemin, attendu) != NO_ID) {
                FAILF("Le précédent du noeud source (<<%s>>) devrait être NO_ID\n",
                        (char*) noeud_donnees(graphe, attendu));
            }
            premiertour = false;
        } else {
            if (precedent_noeud_liste(chemin, attendu) != precedent) {
                FAILF("Le précédent du noeud <<%s>> est <<%s>>, il devrait être le noeud <<%s>>\n",
                        (char*) noeud_donnees(graphe, attendu),
                        (char*) noeud_donnees(graphe, precedent_noeud_liste(chemin, attendu)),
                        (char*) noeud_donnees(graphe, precedent));
            }
        }
        precedent = attendu;
    }
}

int main() {
    INITIALIZE_TESTS();
    SET_ANALYSIS("test_dijkstra.csv");

    BEGIN_SECTION("dijkstra/petits-graphes")
        BEGIN_TESTI("dijkstra-1noeud")
            /*
               -> n1
             */
            struct graphe_t* graphe = creer_graphe(1);
            point_t p1 = { .x = 0.0, .y = 0.0 };
            noeud_id_t n1 = creer_noeud(graphe, p1, "n1");
            liste_noeud_t* chemin;
            float dist = dijkstra(graphe, n1, n1, &chemin);

            ASSERT_EQ_F(dist, 0.f, PRECISION);
            CALL_ASSERT_FUN(check_chemin, graphe, chemin, n1, NO_ID);

            liberer_graphe(&graphe, NULL);
            detruire_liste(&chemin);
        END_TEST

        BEGIN_TESTI("dijkstra-2noeuds")
            /*
                       2
               -> n1 ----> n2
             */
            struct graphe_t* graphe = creer_graphe(2);
            point_t p1 = { .x = 0.0, .y = 0.0 };
            point_t p2 = { .x = 2.0, .y = 0.0 };
            noeud_id_t n1 = creer_noeud(graphe, p1, "n1");
            noeud_id_t n2 = creer_noeud(graphe, p2, "n2");
            ajouter_arrete(graphe, n1, n2);
            liste_noeud_t* chemin;
            float dist = dijkstra(graphe, n1, n2, &chemin);

            ASSERT_EQ_F(dist, 2.f, PRECISION);
            CALL_ASSERT_FUN(check_chemin, graphe, chemin, n1, n2, NO_ID);

            liberer_graphe(&graphe, NULL);
            detruire_liste(&chemin);
        END_TEST

        BEGIN_TESTI("dijkstra-3noeuds")
            /*
                           n3
                            ^
                            | 2
                       2    |
               -> n1 ----> n2
             */
            struct graphe_t* graphe = creer_graphe(3);
            point_t p1 = { .x = 0.0, .y = 0.0 };
            point_t p2 = { .x = 2.0, .y = 0.0 };
            point_t p3 = { .x = 2.0, .y = 2.0 };
            noeud_id_t n1 = creer_noeud(graphe, p1, "n1");
            noeud_id_t n2 = creer_noeud(graphe, p2, "n2");
            noeud_id_t n3 = creer_noeud(graphe, p3, "n3");
            ajouter_arrete(graphe, n1, n2);
            ajouter_arrete(graphe, n2, n3);
            liste_noeud_t* chemin;
            float dist = dijkstra(graphe, n1, n3, &chemin);

            ASSERT_EQ_F(dist, 4.f, PRECISION);
            CALL_ASSERT_FUN(check_chemin, graphe, chemin, n1, n2, n3, NO_ID);

            liberer_graphe(&graphe, NULL);
            detruire_liste(&chemin);
        END_TEST

        BEGIN_TESTI("dijkstra-3noeuds-connexe")
            /*
                       n3
                      / ^
                   5 /  | 4
                    /   |
               -> n1 -> n2
                     3 
             */
            struct graphe_t* graphe = creer_graphe(3);
            point_t p1 = { .x = 0.0, .y = 0.0 };
            point_t p2 = { .x = 3.0, .y = 0.0 };
            point_t p3 = { .x = 3.0, .y = 4.0 };
            noeud_id_t n1 = creer_noeud(graphe, p1, "n1");
            noeud_id_t n2 = creer_noeud(graphe, p2, "n2");
            noeud_id_t n3 = creer_noeud(graphe, p3, "n3");
            ajouter_arrete(graphe, n1, n2);
            ajouter_arrete(graphe, n2, n3);
            ajouter_arrete(graphe, n1, n3);
            liste_noeud_t* chemin;
            float dist = dijkstra(graphe, n1, n3, &chemin);

            ASSERT_EQ_F(dist, 5.f, PRECISION);
            CALL_ASSERT_FUN(check_chemin, graphe, chemin, n1, n3, NO_ID);

            liberer_graphe(&graphe, NULL);
            detruire_liste(&chemin);
        END_TEST

        BEGIN_TESTI("dijkstra-4noeuds")
            /*
                           2
                       n3 --> n4
                      /       ^
                   5 /        | 4
                    /         |
               -> n1 -------> n2
                        5
             */
            struct graphe_t* graphe = creer_graphe(4);
            point_t p1 = { .x = 0.0, .y = 0.0 };
            point_t p2 = { .x = 5.0, .y = 0.0 };
            point_t p3 = { .x = 3.0, .y = 4.0 };
            point_t p4 = { .x = 5.0, .y = 4.0 };
            noeud_id_t n1 = creer_noeud(graphe, p1, "n1");
            noeud_id_t n2 = creer_noeud(graphe, p2, "n2");
            noeud_id_t n3 = creer_noeud(graphe, p3, "n3");
            noeud_id_t n4 = creer_noeud(graphe, p4, "n4");
            ajouter_arrete(graphe, n1, n2);
            ajouter_arrete(graphe, n2, n4);
            ajouter_arrete(graphe, n1, n3);
            ajouter_arrete(graphe, n3, n4);
            liste_noeud_t* chemin;
            float dist = dijkstra(graphe, n1, n4, &chemin);

            ASSERT_EQ_F(dist, 7.f, PRECISION);
            CALL_ASSERT_FUN(check_chemin, graphe, chemin, n1, n3, n4, NO_ID);

            liberer_graphe(&graphe, NULL);
            detruire_liste(&chemin);
        END_TEST

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION()

    BEGIN_SECTION("dijkstra/grilles-5x6")
        /*
                1
           N00 ---> N01 ---> N02 ---> N03 ---> N04
          1 |        |        |        |        |
            v        v        v        v        v
           N10 ---> N11 ---> N12 ---> N13 ---> N14
            |        |        |        |        |
            v        v        v        v        v
           N20 ---> N21 ---> N22 ---> N23 ---> N24
            |        |        |        |        |
            v        v        v        v        v
           N30 ---> N31 ---> N32 ---> N33 ---> N34
            |        |        |        |        |
            v        v        v        v        v
           N40 ---> N41 ---> N42 ---> N43 ---> N44
            |        |        |        |        |
            v        v        v        v        v
           N50 ---> N51 ---> N52 ---> N53 ---> N54
         */
        const int lignes = 6, colonnes = 5;
        struct graphe_t* graphe = creer_graphe(lignes * colonnes);
        noeud_id_t noeuds[lignes * colonnes];

        // Création des noeuds
        for (int i = 0; i < lignes; i++) {
            for (int j = 0; j < colonnes; j++) {
                point_t p = { .x = (float) j, .y = (float) i };
                char nom[12];
                sprintf(nom, "N%d%d", i, j);
                noeuds[i * colonnes + j] = creer_noeud(graphe, p, nom);
            }
        }

        // Création des arrêtes
        for (int i = 0; i < lignes; i++) {
            for (int j = 0; j < colonnes ; j++) {
                if (i < lignes - 1) {
                    ajouter_arrete(graphe, 
                            noeuds[ i      * colonnes + j],
                            noeuds[(i + 1) * colonnes + j]);
                }
                if (j < colonnes - 1) {
                    ajouter_arrete(graphe, 
                            noeuds[ i      * colonnes + j],
                            noeuds[ i      * colonnes + j + 1]);
                }
            }
        }

        BEGIN_TESTI("haut-gauche--bas-droite")
            float dist = dijkstra(graphe, noeuds[0], noeuds[colonnes * lignes - 1], NULL);
            ASSERT_EQ_F(dist, (float)(lignes + colonnes - 2), PRECISION);
        END_TEST

        BEGIN_TESTI("haut-gauche--haut-droite")
            float dist = dijkstra(graphe, noeuds[0], noeuds[colonnes - 1], NULL);
            ASSERT_EQ_F(dist, (float)(colonnes - 1), PRECISION);
        END_TEST

        BEGIN_TESTI("haut-guahce--bas-gauche")
            float dist = dijkstra(graphe, noeuds[0], noeuds[colonnes * (lignes - 1)], NULL);
            ASSERT_EQ_F(dist, (float)(lignes - 1), PRECISION);
        END_TEST

        liberer_graphe(&graphe, NULL);

        REPORT_TO_STDOUT;
        REPORT_ANALYSIS;
    END_SECTION()

    END_ANALYSIS;

    return 0;
}

