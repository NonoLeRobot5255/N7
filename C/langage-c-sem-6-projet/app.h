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
 * @file app.h
 * @brief Module app qui définit et met en relation les composants de l'application.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef APP_H
#define APP_H

#include "graphe.h"
#include "viewport.h"
#include "window.h"
#include "liste_noeud.h"

/** Défini la marge entre le composant de rendu et les bords de la fenêtre */
#define PADDING 30

/** Type (abstrait) de l'application. */
struct app_t;

/**
 * Construit l'application et la configure.
 * La fonction se charge d'allouer dynamiquement tout ce qu'il faut. Par soucis de
 * maintient des responsabilité, c'est toujours ce module qui gère la mémoire.
 * Une fois terminé, il faut donc utiliser @ref terminate_app pour arrêter l'application
 * et libérer convenablement la mémoire.
 *
 * Pré-conditions: 
 *  - width et height positifs strictement
 *  - graph non NULL
 * 
 * @param width largeur de la fenêtre (en pixels)
 * @param height hauteur de la fenêtre (en pixels)
 * @param graph graphe à représenter
 * @return pointeur sur l'application, allloué dans le tas
 */
struct app_t* setup_app(int width, int height, struct graphe_t* graph);

/**
 * Lance l'application, ce qui a pour conséquence d'ouvrir la fenêtre et de
 * commencer le rendu.
 *
 * Cette fonction ne retourne qu'une fois que les threads principaux sont lancés
 * (en théorie). Il ne faut surtout pas l'appeler plusieurs fois, ça causerait des
 * problèmes.
 *
 * Pré-conditions: app non NULL, app non déjà lancée
 *
 * @param app application (construite avec @ref setup_app)
 */
void launch_app(struct app_t* app);

/**
 * "Rafraîchit" l'affichage, c'est-à-dire recalcul l'apparence des composants et
 * les affiche dans la fenêtre. Cette fonction est non blocante, car elle se contente
 * de réveiller le thread de rendu principal (@ref refresh_window). Le rendu est
 * assez rapide car il n'y a pas vraiment de "calcul", c'est cette fonction qui est
 * utilisée pour mettre à jour la fenêtre avec les nouvelles coordonnées du curseur,
 * la nouvelle apparence des tuiles de la mosaïque, etc.
 *
 * Pré-conditions: app non NULL, app lancée
 *
 * @param app application à rafraîchir
 */
void refresh_app(struct app_t* app);

/**
 * Bouge le curseur aux coordonnées indiquées et rafraîchit l'application.
 * Les coordonnées sont typiquement obtenues à partir d'un event SDL.
 *
 * Pré-conditions: app non NULL, app lancée
 *
 * @param app application à mettre à jour
 * @param x coordonnée x (de fenêtre)
 * @param y coordonnée y (de fenêtre)
 */
void move_cross_app(struct app_t* app, int x, int y);

/**
 * Termine l'application (donc chacun de ses threads) et libère la mémoire allouée.
 * Cette fonction est blocante car elle attend la fin de chacun des threads (pas
 * de détachement).
 *
 * Si l'application s'interbloque c'est probablement ici... Normalement j'ai corrigés
 * la plupart des "gros" problèmes mais avec la programmation concurrente on est jamais
 * à l'abris :( .
 *
 * Pré-conditions: app_ptr pointe sur une app non NULL et lancée
 * Post-conditions: `*app_ptr` = NULL
 *
 * @param app_ptr pointeur sur l'application
 */
void terminate_app(struct app_t** app_ptr);

/**
 * Type synonyme pour les pointeurs de fonction définissant une *tâche*.
 * Une tâche est une fonction qui prend un état interne en paramètre et
 * retourne un code d'erreur (ou 0 si tout s'est bien passé).
 */
typedef int(*task_fun_t)(struct app_t*,void*);
/**
 * Type synonyme pour les pointeurs de fonction définissant un "post traitement".
 * La fonction prend en paramètre l'app (pour faire du rendu, typiquement) et l'état
 * obtenu à la suite de l'appel de la tâche, et retourne un code d'erreur ou 0
 * si tout s'est bien passé.
 */
typedef int(*post_task_fun_t)(struct app_t*,void*);

/**
 * Exécute la tâche donnée (puis le traitement post-tâche, le cas échéant) dans un thread
 * à part. Si une tâche était déjà en cours, attend qu'elle soit terminée (on ne peut
 * lancer qu'une tâche à la fois), sinon lance le thread et retourne immédiatement.
 *
 * Si la fonction task renvoie un code non nul, le thread est interrompu et retourne ce
 * code. Sinon, l'userdata est donné à la fonction post-tâche (si elle n'est pas NULL).
 *
 * De même, si la fonciton post tâche renvoie un code non nul, le thread est interrompu et
 * retournce ce code d'erreur. Sinon, le thread retourne 0.
 *
 * L'argument `detach` indique si le thread créé est à _détacher_ ou non. Si le thread est détaché,
 * sa teminaison n'est pas gérée par l'application. On s'attend alors à ce que le thread termine
 * tout seul (à utiliser avec parcimonie donc).
 *
 * Pré-conditions : app non NULL, app lancée
 *
 * @param app application associée à la tâche
 * @param task fonction de la tâche
 * @param post fonction de traitement post-tâche
 * @param userdata données utilisée dans la tâche et/ou la post-tâche
 * @param detach mettre à true si on veut que le thread soit détaché après la création
 */
void exec_task_app(struct app_t* app, task_fun_t task, post_task_fun_t post, void* userdata, bool detach);

/**
 * Demande au composant qui affiche le graphe de mettre en évidence le chemin donné (sous
 * forme de liste de noeud).
 *
 * Mettre NULL ici retire la mise en évidence.
 *
 * Pré-conditions : app non NULL, app lancée
 *
 * @param app application contenant le graphe
 * @param path chemin à mettre en évidence, sous forme d'une liste_noeud_t
 */
void highlight_path_app(struct app_t* app, liste_noeud_t* path);

/**
 * Demande au composant qui affiche le graphe de changer le style du noeud donné avec la couleur
 * donnée (d'arrière plan).
 *
 * Pré-conditions : app non NULL, app lancée
 *
 * @param app application contenant le graphe
 * @param node identifiant du noeud dont on veut changer la couleur
 * @param color couleur associée au noeud
 */
void highlight_node_app(struct app_t* app, noeud_id_t node, SDL_Color color);

/**
 * Demande au composant qui affiche le graphe de mettre l'arrête donnée en valeur.
 * Il ne peut y avoir qu'une seule arrête mise en valeur. Si source et destination
 * ne correspondent pas à un arc du graphe, aucune arrête n'est colorée (pour retirer la
 * mise en évidence typiquement).
 *
 * Pré-conditions : app non NULL, app lancée
 *
 * @param app application contenant le graphe
 * @param source source de l'arc
 * @param destination destination de l'arc
 */
void highlight_edge_app(struct app_t* app, noeud_id_t source, noeud_id_t destination);

#endif // APP_H



