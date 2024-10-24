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
 * @file graphe_parse.h
 * @brief Module `graphe_parse` qui permet de praser un fichier texte décrivant un graphe.
 *
 * Le langage reconnu par le parseur est le suivant (en forme EBNF) :
 * @code
 * graphe = section noeuds, { "\n" }, section liens
 * section noeuds = 'Noeuds:', "\n", { noeud }
 * section liens  = 'Liens:', "\n", { lien }
 *
 * noeud = "-", identifiant, ":", "(", nombre, ",", nombre, ")", "\n"
 * lien  = "-", identifiant, "->", identifiant, "\n"
 * @endcode
 *
 * Avec `identifiant` toute chaîne sans ':' et sans '->', et `nombre` un nombre flottant
 * valide (incluant en notation scientifique).
 *
 * Le parseur ignore les espaces simples (" ") en dehors des identifiants mais les retours 
 * à la ligne sont importants.
 *
 * Une description de noeud se compose donc d'une liste de noeuds, chacun étant un nom associé à un
 * couple (sa position).
 *
 * Une description de lien est de la forme `- A -> B` ou `- A -- B` avec A et B des noeuds préalablement 
 * définis. Dans le cas `->` un arc de A vers B est créé ; dans le cas `--` l'arc A vers B et B vers A
 * sont tous deux créés (pour faciliter l'écriture).
 *
 * Un graphe se compose de la section des noeuds puis de la section des liens (dans cet ordre).
 * Les lignes vides sont ignorées.
 *
 * Voici un example :
 * @code
 * Noeuds:
 * - k1: (1.0,2.0)
 * - k2: (1.0,3.0)
 * - k3: (2.0,5.0)
 * 
 * Liens:
 * - k1 -> k2
 * - k1 -> k3
 * - k2 -- k3
 * @endcode
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef GRAPHE_PARSE_H
#define GRAPHE_PARSE_H

#include "graphe.h"

/**
 * Fonction qui parse le fichier dont le nom est passé en paramètre.
 * La fonction se charge toute seule d'ouvrir et de fermer le fichier, puis
 * crée un graphe et le peuple avec les informations qui en sont issues (voir
 * introduction du module pour une description de la syntaxe).
 *
 * En cas d'erreur, la fonction affiche une erreur sur `stderr` et renvoie NULL.
 *
 * Le graphe alloué a pour information sur les noeuds (dans le "noeud données") le
 * nom du noeud tel que fourni dans le fichier.
 *
 * @param filename fichier à parser
 * @return graphe résultant du parsing, ou NULL si problème
 */
struct graphe_t* parser_graphe(const char* filename);



#endif // GRAPHE_PARSE_H



