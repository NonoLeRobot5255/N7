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
 * @file graphe.h
 * @brief Module graphe, qui définit un graphe orienté, dans les noeuds duquel sont
 * stocké une position cartésienne et des données utilisateurs (un nom, par exemple).
 *
 * Les graphes sont implantés avec des tableaux (pour des raisons de practicités et
 * parce que le projet est autrement dépourvu de toute structure chaînée). Une conséquence
 * de cela est que l'on doit donner le nombre (maximum) de noeuds présents dans le graphe.
 * Dans ce sens, les graphes sont plutôt des objets statiques ("immutables" d'une certaine
 * façon).
 *
 * Le type pour les graphes est complètement abstrait. L'utilisateur n'a pas accès aux
 * noeuds directement, mais à des _identifiants_ de noeud (@ref noeud_id_t).
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef GRAPHE_H
#define GRAPHE_H

#include "point.h"
#include <stdlib.h>
#include <stdio.h>

/** Identifiant spécial correspondant à un identifiant invalide, un noeud non trouvé, etc. */
#define NO_ID   0

/** Type pour les identifiants de noeud. */
typedef unsigned long noeud_id_t;

/** Type abstrait du graphe. */
struct graphe_t;

/**
 * Crée un graphe avec le nombre (maximal) de noeuds donné. Le graphe est alloué sur
 * le tas.
 *
 * Cas d'erreur : `nombre_noeuds` < 65536 (si == 0, comportement indéfini)
 * => un message d'erreur est affiché et la fonction renvoie NULL
 *
 * @param nombre_noeuds nombre maximum de noeuds dans le graphe
 * @return graphe créé
 */
struct graphe_t* creer_graphe(size_t nombre_noeuds);

/**
 * Créer un noeud dans le graphe, avec la position et les données utilisateur données.
 * La fonction renvoie l'identifiant du noeud créé en cas de succès ou @ref NO_ID si la 
 * création n'est pas possible (car plus de place typiquement), 
 *
 * Pré-conditions : graphe non NULL
 *
 * @param graphe graphe dans lequel créer le noeud
 * @param position position cartésienne du noeud
 * @param donnees données utilisateur à stocker sur le noeud
 * @return identifiant du noeud créé, ou @ref NO_ID si pas de noeud créé
 */
noeud_id_t creer_noeud(struct graphe_t* graphe, point_t position, void* donnees);

/**
 * Ajouter une arrête dans le graphe entre les noeuds donnés. La fonction renvoie vrai si
 * l'ajout a été réalisé et faux sinon (typiquement, les noeuds n'existent pas ou il n'y
 * a plus de place pour les arrêtes).
 *
 * Pré-conditions : graphe non NULL
 *
 * @param graphe graphe dans lequel ajouter l'arrête
 * @param source source de l'arc
 * @param destination de l'arc
 * @return vrai si l'arc a été ajouté, faux sinon
 */
bool ajouter_arrete(struct graphe_t* graphe, noeud_id_t source, noeud_id_t destination);

/**
 * Libérer le graphe alloué en mémoire par @ref creer_graphe. La fonction admet une fonction
 * de libération customisée pour libérer les données utilisateur (si elles ont été allouées
 * sur le tas, typiquement). Cette fonction peut être NULL, auquel cas les données utilisateurs
 * sont laissées telle quelles.
 *
 * Pré-conditions : graphe != NULL
 * Post-conditions : *graphe == NULL
 *
 * @param graphe pointeur sur le graphe à libérer
 * @param liberer_donnees fonction à appeler sur les données utilisateur stockées sur les noeuds ;
 *   cette fonction prend en paramètre les données à libérer
 */
void liberer_graphe(struct graphe_t** graphe, void (*liberer_donnees)(void*));

/**
 * Retourne le nombre de noeuds dans le graphe.
 * Pré-conditions : graphe non NULL
 * @param graphe graphe
 * @return nombre de noeuds dans graphe
 */
size_t nombre_noeuds(const struct graphe_t* graphe);

/**
 * Récupère les noeuds du graphe (sous la forme d'identifiants). Les noeuds
 * sont stockés dans le tableau passé en paramètre, qui doit être de taille
 * suffisante (au moins égale au résultat de @ref nombre_noeuds). L'allocation
 * et les désallocation du tableau est laissée à la charge de l'utilisateur.
 *
 * Pré-conditions : graphe non NULL, noeuds non NULL, noeuds de taille suffisante
 *
 * @param graphe graphe dont on veut les noeuds
 * @param noeuds [out] tableau pour recevoir les noeuds du graphe
 */
void noeuds(const struct graphe_t* graphe, noeud_id_t* noeuds);

/**
 * Renvoie vrai ssi les noeuds donnés sont _voisins_ dans le graphe. B est un voisin de A
 * ssi il existe un arc (orienté) dont l'origine est A et la destination est B.
 *
 * Si les noeuds sont invalides, renvoie nécessairement faux.
 *
 * Pré-conditions : graphe non NULL
 *
 * @param graphe graphe dans lequel faire le test
 * @param noeuda noeud source
 * @param noeudb noeud destination (dont on veut savoir s'il est voisin de la source)
 * @return vrai ssi noeudb voisin de noeuda
 */
bool est_voisin(const struct graphe_t* graphe, noeud_id_t noeuda, noeud_id_t noeudb);

/**
 * Renvoie le nombre de voisins du noeud.
 * Pré-conditons : graphe non NULL
 * @param graphe graphe dans lequel on cherche les voisins
 * @param noeud noeud dont on veut le nombre de voisins
 * @return nombre de voisins du noeud
 */
size_t nombre_voisins(const struct graphe_t* graphe, noeud_id_t noeud);

/**
 * Récupère les noeuds voisins du noeud donné. Les noeuds sont stockés dans le
 * tableau passé en paramètre, qui doit être de taille suffisante (au moins égale 
 * à @ref nombre_voisins).
 *
 * Pré-conditions : graphe non NULL, voisins non NULL, de taille suffisante
 * Post-conditions : pour tout i, 0 <= i < nombre_voisins(graphe, noeud), 
 *                      est_voisin(graphe, noeud, voisins[i])
 *
 * @param graphe graphe dans lequel chercher le noeud
 * @param noeud noeud dont on veut les voisins
 * @param voisins [out] noeuds voisins du noeud
 */
void noeuds_voisins(const struct graphe_t* graphe, noeud_id_t noeud, noeud_id_t* voisins);

/**
 * Récupère les données utilisateurs associée au noeud, transmises au moment de l'appel à
 * @ref creer_noeud. S'il n'y a pas de donnée pour le noeud ou si le noeud est invalide,
 * retourne NULL.
 *
 * Pré-conditions : graphe non NULL
 *
 * @param graphe graphe où chercher le noeud
 * @param noeud noeud dont on veut les données
 * @return données utilisateurs ou NULL s'il n'y en a pas
 */
void* noeud_donnees(const struct graphe_t* graphe, noeud_id_t noeud);

/**
 * Récupère la position cartésienne du noeud donné.
 * Si le noeud est invalide, le point retourné est non-spécifié.
 *
 * Pré-conditions : graphe non NULL
 *
 * @param graphe graphe dans lequel chercher le noeud
 * @param noeud noeud dont on veut la position
 * @return position cartsienne du noeu
 */
point_t noeud_position(const struct graphe_t* graphe, noeud_id_t noeud);

/**
 * Calcule la distance directe entre deux noeuds, c'est-à-dire la distance entre leurs
 * positions _s'ils sont voisins_. La fonction retourne `INFINITY` si les noeuds ne sont
 * pas voisins, et `NAN` si au moins l'un des deux noeuds est invalide.
 * 
 * Pré-conditions : graphe non NULL
 *
 * @param graphe graphe dans lequel chercher les noeuds
 * @param noeuda noeud source
 * @param noeudb noeud destination
 * @return distance entre les positions respectives de noeudb et noeuda si noeudb est
 * voisin de noeuda, `INFINITY` s'ils ne sont pas voisins, `NAN` si noeuda ou noeudb est
 * invalide
 */
float noeud_distance(const struct graphe_t* graphe, noeud_id_t noeuda, noeud_id_t noeudb);


/**
 * Informations sur le noeud en train d'être visité, passées en paramètre de la fonction
 * donnée à l'itérateur @ref pour_chaque_noeud ou @ref trouver_noeud.
 */
struct noeud_info_t {
    /** Identifiant du noeud en cours de visite */
    noeud_id_t id;
    /** Position cartésienne du noeud en cours de visite */
    point_t position;
    /** Données utilisateurs stockées sur le noeud */
    void* noeud_data;
};

/**
 * Type pour la fonction appelée sur chaque noeud par @ref pour_chaque_noeud.
 * Les fonctions de ce type prennent en paramètre un @ref noeud_info_t qui
 * correspond aux informations du noeud en cours de visite, ainsi que des données
 * utilisateurs, transmises via @ref pour_chaque_noeud.
 */
typedef void(*noeud_iterateur)(struct noeud_info_t,void*);

/**
 * Type pour une fonction sur les noeuds qui retourne un booléen, appelée par
 * @ref trouver_noeud. Les fonctions de ce type reçoivent les informations du noeud 
 * en cours de visite, ainsi que des données utilisateur transmises par 
 * @ref trouver_noeud.
 */
typedef bool(*noeud_predicat)(struct noeud_info_t,void*);

/**
 * Informations sur l'arrête en train d'être visitée, passées en paramètre de la fonction
 * donnée à l'itérateur @ref pour_chaque_arrete.
 */
struct arrete_info_t {
    /** Noeud source de l'arc */
    noeud_id_t id_source, 
    /** Noeud destination de l'arc */
               id_destination;
    /** Position du noeud source de l'arc */
    point_t position_source, 
    /** Position du noeud destination de l'arc */
            position_destination;
    /** Données utilisateur associées au noeud source */
    void* noeud_data_source;
    /** Données utilisateur associées au noeud destination */
    void* noeud_data_destination;
};

/**
 * Type pour une fonction sur les arrêtes, utilisée par @ref pour_chaque_arrete.
 * Les fonctions de ce type reçoivent les informations sur l'arrête en cours de visite, ainsi
 * que des données utilisateurs transmises par @ref pour_chaque_arrete
 */
typedef void(*arrete_iterateur)(struct arrete_info_t,void*);

/**
 * Trouver un noeud qui respecte le prédicat passé en paramètre. Cette fonction renvoie l'identifiant
 * du noeud trouvé, ou @ref NO_ID si aucun noeud n'a été trouvé.
 *
 * Pré-conditions : graphe non NULL, predicat non NULL
 * Post-conditions : si resultat != NO_ID, alors resultat est un noeud de graphe et predicat(resultat)
 * (modulo effets de bord)
 *
 * @param graphe graphe dans lequel chercher
 * @param predicat critère de recherche
 * @param userdata donnée utilisateur à transmettre à predicat
 * @return identifiant du noeud trouvé (ou @ref NO_ID si pas trouvé)
 */
noeud_id_t trouver_noeud(const struct graphe_t* graphe, noeud_predicat predicat, void* userdata);

/**
 * Parcours les noeuds du graphe (une fois) et applique la fonction donnée à chacun d'entre
 * eux.
 *
 * Pré-conditions : graphe non NULL, iterateur non NULL
 *
 * @param graphe graphe à parcourir
 * @param iterateur fonction à appliquer sur chaque noeud
 * @param userdata données utilisateur à passer à l'itérateur
 */
void pour_chaque_noeud(struct graphe_t* graphe, noeud_iterateur iterateur, void* userdata);

/**
 * Parcours les arrêtes du graphe (une fois) et applique la fonction donnée à chacune d'entre
 * elles.
 *
 * Pré-conditions : graphe non NULL, iterateur non NULL
 *
 * @param graphe graphe à parcourir
 * @param iterateur fonction à appliquer sur chaque arrête
 * @param userdata données utilisateur à passer à l'itérateur
 */
void pour_chaque_arrete(struct graphe_t* graphe, arrete_iterateur iterateur, void* userdata);

/**
 * Exporte un graphe au format DOT de Graphviz sur le fichier donné. Les données utilisateur
 * exportées vers le fichier à l'aide de la fonction `afficher_donnees` fournie par l'utilisateur.
 * Si cette dernière est nulle, les données ne sont pas exportées.
 *
 * Pré-conditions : graphe non NULL, sortie non NULL et fichier ouvert
 *
 * @param graphe graphe à exporter
 * @param sortie fichier vers lequel exporter les données
 * @param afficher_donnees fonction qui exporte les données utilisateur vers la sortie ; elles
 *          apparaissent sous la forme de tooltip dans le graphe
 */
void exporter_dot(const struct graphe_t* graphe, FILE* sortie, void(*afficher_donnees)(FILE*,void*));


#endif // GRAPHE_H



