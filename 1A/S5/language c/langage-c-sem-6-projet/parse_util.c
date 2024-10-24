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
 * @file parse_util.c
 * @brief Implantation du module `parse_util`
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "parse_util.h"
#include <stdio.h>
#include <string.h>
#include <stdarg.h>

/**
 * Renvoie vrai ssi le caractère c est un délimiteur.
 * Les délimiteurs sont globalement les espaces et la ponctuation.
 * @param c caractère à tester
 * @return vrai ssi c est un délimiteur
 */
static bool delimiteur(char c) {
    if (c == '\0') {
        return true;
    }

    static const char delims[] = " \t\r\n:.;,!()[]{}#?/\\~&+=$";
    size_t i = 0;
    while (delims[i] != '\0' && delims[i] != c) {
        i++;
    }

    return delims[i] != '\0';
}

bool est_espace(char c) {
    return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

void manger_espaces(const char* str, size_t* i) {
    /* != '\0' n'est pas utile c'est juste pour la lisibilité */
    while (str[*i] != '\0' && est_espace(str[*i])) { 
        *i = *i + 1; 
    }
}

bool parser_jusqua(const char* str, size_t* i, char c) {
    while (str[*i] != '\0' && str[*i] != c) {
        *i = *i + 1;
    }
    return str[*i] != '\0';
}

bool parser_jusqua2(const char* str, size_t* i, char c1, char c2) {
    while (str[*i] != '\0' && str[*i + 1] != '\0' && !(str[*i] == c1 && str[*i + 1] == c2)) {
        *i = *i + 1;
    }
    return str[*i + 1] != '\0';
}

/**
 * Type interne pour représenter si un token est borné ou non.
 */
enum token_mode {
    BORNE, NON_BORNE
};

int commence(const char* entree, ...) {
    va_list args;
    bool cue = true;
    int resultat = -1;

    va_start(args, entree);

    const char* token;
    size_t i = 0, taille_entree = strlen(entree);

    while (cue && i < taille_entree) {
        token = va_arg(args, const char*);

        if (token == NULL) {
            cue = false;
        } else {
            size_t taille_token = strlen(token);
            manger_espaces(entree, &i);
            
            // Déterminer si le token est borné
            enum token_mode mode;
            if (taille_token > 1 && token[taille_token - 2] == '\\' && token[taille_token - 1] == '>') {
                mode = BORNE;
                taille_token -= 2; // On retire le marqueur de borne
            } else {
                mode = NON_BORNE;
            }

            // Tester si la chaîne correspond au token
            if (strncmp(token, entree + i, taille_token) == 0) { // token trouvé
                i += taille_token;
                resultat = (int) i;
                if (mode == BORNE && !delimiteur(entree[i])) {
                    cue = false;
                    resultat = -1;
                }
            } else {
                cue = false;
                resultat = -1;
            }
        }
    }

    return resultat;
}




