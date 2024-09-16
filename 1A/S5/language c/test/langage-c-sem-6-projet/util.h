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
// dijkstra - Copyright (c) 2023 Guillaume Dupont
// Contact: <guillaume.dupont@toulouse-inp.fr>
/**
 * @file util.h 
 * @brief Quelques macros utilitaires (pas vraiment un module)
 *
 * @author G. Dupont
 * @version 1.0
 */
#ifndef UTIL_H
#define UTIL_H

/** Stringify un token  */
#define ___str(s)   #s
/** Macro de wrapping pour que la stringification se passe bien */
#define __str(s)    ___str(s)

/** Minimum arithmétique entre deux valeurs */
#define MIN(x, y)   (x > y ? y : x)
/** Maximum arithmétique entre deux valeurs */
#define MAX(x, y)   (x > y ? x : y)
/** Écrétage d'une valeur entre deux valeurs (si x est en dessous de down, ramène
 * x à down, si x est au dessus de up, ramène x à up, sinon, laisse x inchangé).
 */
#define CLAMP(x, down, up)  (x >= up ? up : (x <= down ? down : x))

/** Rcupère la norme 2 d'un vecteur de dimension 2 */
#define NORM(x, y)  sqrt((x)*(x) + (y)*(y))

#ifdef _DEBUG // Les fonctionnalités suivantes sont activées seulement en mode debug
#include <stdlib.h>

/** Écrit un message de débug avec le numéro du thread, à la printf */
#define TLog(...)           { printf("[thread-%08lx] ", SDL_ThreadID()); printf(__VA_ARGS__); putchar('\n'); }
/** Écrit un message de débug préfixé par "main" (pour le thread principal), à la printf */
#define MLog(...)           { printf("[main] "); printf(__VA_ARGS__); putchar('\n'); }
#else
/** Écrit un message de débug avec le numéro du thread (ne fait rien dans cette configuration) */
#define TLog(...)           {}
/** Écrit un message de débug préfixé par "main" (ne fait rien dans cette configuration) */
#define MLog(...)           {}
#endif

#endif // UTIL_H


