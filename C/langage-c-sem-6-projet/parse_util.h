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
 * @file parse_util.h
 * @brief Module `parse_util` avec quelques fonctions utilitaires pour parser
 * des machins.
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef PARSE_UTIL_H
#define PARSE_UTIL_H

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>

/**
 * Renvoie vrai si c est un caractère de type espace.
 * Les caractères de type espace sont l'espace blanc (`' '`), la
 * tabulation (`'\\t'`) et les caractères de retour à la ligne (`'\\n'`, `'\\r'`).
 * @param c caractère à tester
 * @return vrai ssi c est un espace
 */
bool est_espace(char c);

/**
 * Faire progresser l'indice passé en paramètre jusqu'à ce qu'il corresponde 
 * à un caractère non-espace dans la chaîne donnée.
 *
 * Pré-conditions : str non NULL, i non NULL
 * Post-conditions : `*i > \\old(*i)`, `str[*i] == 0` ou `str[*i]` non espace
 *
 * @param str chaîne à processer
 * @param i pointeur sur l'indice à faire varier
 */
void manger_espaces(const char* str, size_t* i);

/**
 * Teste si la chaîne donnée commence par les tokens donnés (sous forme d'une
 * liste de chaînes de caractère terminée par un NULL).
 *
 * La fonction ignore naturellement les espaces (caractères validant `est_espace`) et
 * retourne l'indice après lequel le dernier token a été trouvé, ou -1 si la ligne ne
 * commence pas par _tous_ les tokens donnés.
 *
 * Si un token se termine par `\>` on considère qu'il est _borné_, c'est à dire que le
 * token s'arrête lorsqu'on rencontre un délimiteur.
 * Par exemple : `commencer("abc:", "abc", NULL)` renvoie -1, mais 
 * `commencer("abc:", "abc\\>", NULL)` renvoie 3
 *
 * @param entree chaîne à vérifier
 * @return indice de la fin du dernier token ou -1 si la chaîne ne commence pas par
 * les token donnés
 */
int commence(const char* entree, ...);

/**
 * Parse la chaîne en incrémentant l'indice passé en paramètre jusqu'à ce que le
 * caractère à l'indice `*i` soit c. Le fonction retourne vrai ssi le caractère c
 * a été rencontré, et alors `str[*i] == c`.
 *
 * @param str chaîne à parcourir
 * @param i indice à incrémenter
 * @param c caractère jusqu'au quel incrémenter l'indice
 * @return vrai ssi c est présent dans la chaîne
 */
bool parser_jusqua(const char* str, size_t* i, char c);

/**
 * Parse la chaîne en incrémentant l'indice passé en paramètre jusqu'à ce que les
 * deux caractères consécutifs soient c1 puis c2. Retourne vrai ssi les caractères
 * sont présents dans la chaîne.
 *
 * Dit autrement : si le résultat est vrai, alors `str[*i] == c1` et `str[*i + 1] == c2`
 *
 * @param str chaîne à parcourir
 * @param i indice à incrémenter
 * @param c1 première caractère
 * @param c2 deuxième caractère
 * @return vrai ssi c1c2 présent dans chaîne
 */
bool parser_jusqua2(const char* str, size_t* i, char c1, char c2);


#endif // PARSE_UTIL_H


