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
 * @file window.c 
 * @brief Implantation du module window.
 *
 * Attention ça parle de concurrence et de synchro c'est vachement pas simple.
 *
 * @author G. Dupont
 * @version 1.0
 */
#include "window.h"
#include "util.h"
#include <SDL2/SDL2_gfxPrimitives.h>
#include <SDL2/SDL_ttf.h>
#include <math.h>

/** Taille initial du registre des polices */
#define INITIAL_FONTREG_SIZE    4

/**
 * Implémenation du type pour la fenêtre. Contient principalement une `SDL_Window` et
 * son `SDL_Renderer`, une texture cible représentant le contenu de la fenêtre, la
 * fonction `repaint` donnée par l'utilisateur et diverses choses pour la concurrence.
 */
struct window_t {
    /** Largeur de la fenêtre. */
    int w, 
    /** Hautuer de la fenêtre */
        h;
    /** Titre de la fenêtre. */
    const char* name;

    /** Objet SDL représentant la fenêtre. */
    SDL_Window* window;
    /** Renderer associé à la fenêtre. */
    SDL_Renderer* renderer;
    /** Texture cible du contenu de la fenêtre, sur laquelle le rendu est effectué. */
    SDL_Texture* target;
    /** Couleur de fond */
    SDL_Color background;

    /** Ensemble des polices chargées */
    TTF_Font** loaded_fonts;
    /** Taille du registre des polices chargées */
    int fontreg_size;

    /** Callback pour rendre les éléments dans la fenêtre, appelé par le render thread. */
    repaint_fn repaint;
    /** Données utilisateur passées au moment de créer la fenêtre et transmises au callback. */
    void* userdata;
    
    /** Le render thread. */
    SDL_Thread* render_thread;
    /** Verrour sur cet enregistrement (partagé entre le thread principal et le render thread */
    SDL_mutex* mutex;
    /** Sémaphore qui indique la fenêtre est "prête", autrement dit qu'elle a terminé l'initialisation
     * et la tâche de rafraîchissement (signalisé par la fenêtre).
     */
    SDL_sem* ready;
    /** Sémaphore pour "réveiller" la fenêtre et initier le rafraîhcissement (en attente par le
     * render thread).
     */
    SDL_sem* wake_up;

    /** Commande pour stopper la fenêtre (si stop == true au prochian réveil le render-thread se termine). */
    bool stop;
};

static void color_restore(struct window_t* window) {
    SDL_SetRenderDrawColor(window->renderer, 
            window->background.r, window->background.g, window->background.b, window->background.a);
}

/**
 * Fonction du render thread qui réalise la gestion du rafraîchissement de la fenêtre.
 *
 * Pour des raisons de cohérence du multi-threading, c'est en fait cette fonction qui se 
 * charge de configurer la fenêtre (créer le `SDL_Window` et associés). De cette façon, on
 * est sûr que la texture cible, le renderer et les textures crées pour le rafraîchissement
 * sont bien dans le même thread.
 *
 * @param userdata donnée utilisateurs passées au moment de la création du thread, qui contiennent
 *      ici une référence vers la window à laquelle le thread est attachée.
 */
static int do_render(void* userdata) {
    TLog("Starting main render thread");
    struct window_t* window = (struct window_t*) userdata;

    // La suite est un peu technique : on lock la window pour la configurer
    // Au moment de la levée du lock, on est sûr que les champs de window ne sont
    // pas NULL.
    SDL_LockMutex(window->mutex);
    window->stop = false;
    SDL_CreateWindowAndRenderer(
            window->w, window->h, 0 /* SDL_WINDOW_RESIZEABLE */,
            &window->window, &window->renderer
        );
    if (window->name != NULL) {
        SDL_SetWindowTitle(window->window, window->name);
    }
    // La texture cible (sur laquelle toutes les autres seront rendues)
    window->target = SDL_CreateTexture(window->renderer, 0, SDL_TEXTUREACCESS_TARGET, window->w, window->h);
    SDL_SetRenderDrawBlendMode(window->renderer, SDL_BLENDMODE_BLEND);
    SDL_SetTextureBlendMode(window->target, SDL_BLENDMODE_BLEND);
    SDL_UnlockMutex(window->mutex);

    bool cue = true;

    // Boucle principale
    while (cue) {
        SDL_SemPost(window->ready);         // On signale que l'on est prêt
        SDL_SemWait(window->wake_up);       // On attend d'être réveillé

        // Zone critique (fenêtre lockée)
        SDL_LockMutex(window->mutex);
        cue = !window->stop; // On regarde si on doit s'arrêter
        SDL_UnlockMutex(window->mutex); // Fin de zone critique (on fait un lock en deux temps pour être plus
                                        // efficace)

        if (cue) {
            // Zone critique (fenêtre lockée)
            SDL_LockMutex(window->mutex);

            // Mise en place de la texture cible comme texture principale
            // (et nettoyage de la fenêtre pour éviter les superpositions)
            SDL_SetRenderTarget(window->renderer, window->target);
            //SDL_SetRenderDrawColor(window->renderer, 0, 0, 0, 0);
            color_restore(window);
            SDL_RenderClear(window->renderer);

            // Appel au callback
            if (window->repaint != NULL) {
                window->repaint(window, window->userdata);
            }
            
            // On remet la texture par défaut et on présente la fenêtre
            // (utilisation du système de frame buffer de SDL)
            SDL_SetRenderTarget(window->renderer, NULL);
            color_restore(window);
            //SDL_SetRenderDrawColor(window->renderer, 0, 0, 0, 0);
            SDL_RenderClear(window->renderer);
            SDL_RenderCopy(window->renderer, window->target, NULL, NULL);
            SDL_RenderPresent(window->renderer);

            // Fin de la zone critique
            SDL_UnlockMutex(window->mutex);
        }
    }

    TLog("Ending render thread");

    // Libération de la mémoire
    SDL_LockMutex(window->mutex);
    SDL_DestroyTexture(window->target);
    SDL_DestroyRenderer(window->renderer);
    SDL_DestroyWindow(window->window);
    SDL_UnlockMutex(window->mutex);

    return 0;
}


struct window_t* create_window(int w, int h, const char* name, repaint_fn repaint, void* userdata) {
    struct window_t* win = (struct window_t*) malloc(sizeof(struct window_t));
    win->w = w;
    win->h = h;
    win->name = name;

    // On ne crée pas ces éléments tout de suite car on veut les créer dans le render thread !
    win->window = NULL;
    win->renderer = NULL;
    win->target = NULL;

    win->fontreg_size = INITIAL_FONTREG_SIZE;
    win->loaded_fonts = (TTF_Font**)malloc(win->fontreg_size * sizeof(TTF_Font*));
    for (int i = 0; i < win->fontreg_size; i++) {
        win->loaded_fonts[i] = NULL;
    }

    win->repaint = repaint;
    win->userdata = userdata;

    win->render_thread = NULL;
    win->mutex = SDL_CreateMutex();
    win->ready = SDL_CreateSemaphore(0);
    win->wake_up = SDL_CreateSemaphore(0);

    win->stop = true;

    return win;
}

void start_window(struct window_t* window) {
    SDL_LockMutex(window->mutex);
    SDL_Thread* th = SDL_CreateThread(do_render, "render-thread", window);
    window->render_thread = th;
    SDL_UnlockMutex(window->mutex);
    SDL_SemWait(window->ready); // Le sémaphore est signalisé lorsque le thread rentre dans la boucle
                                // (ce qu'il fait que si il a fini son initialisation)
}

void stop_window(struct window_t** window_ptr) {
    struct window_t* window = *window_ptr;
    SDL_LockMutex(window->mutex);
    window->stop = true;
    SDL_UnlockMutex(window->mutex);

    SDL_SemPost(window->wake_up);
    SDL_WaitThread(window->render_thread, NULL);
    SDL_DestroyMutex(window->mutex);
    SDL_DestroySemaphore(window->wake_up);
    SDL_DestroySemaphore(window->ready);

    for (int i = 0; i < window->fontreg_size; i++) {
        if (window->loaded_fonts[i] != NULL) {
            TTF_CloseFont(window->loaded_fonts[i]);
        }
    }
    free(window->loaded_fonts);

    free(window);
    *window_ptr = NULL;
}

void refresh_window(struct window_t* window) {
    SDL_SemPost(window->wake_up);
}

/**
 * Fonction auxiliaire qui vérifie que le thread courant est bien le render thread
 * de la window.
 *
 * Cette fonction ne fait quelque chose que si `STATIC_THREADING` est activé (sinon 
 * elle ne fait rien).
 *
 * Si le thread n'est pas bon, cela compte comme une erreur critique et le programme
 * est quitté brutalement avec le code d'erreur -1.
 *
 * @param window fenêtre dont on veut vérifier la cohérence du thread
 */
static void test_thread(struct window_t* window) {
#ifdef STRICT_THREADING
    if (SDL_GetThreadID(window->render_thread) != SDL_ThreadID()) {
        puts("Error: cannot create texture from other thread");
        exit(-1);
    }
#else
    (void) window;
#endif
}

SDL_Texture* create_texture(struct window_t* window, uint32_t format, int access, int w, int h) {
    test_thread(window);
    return SDL_CreateTexture(window->renderer, format, access, w, h);
}

SDL_Texture* create_texture_from_surface(struct window_t* window, SDL_Surface* surface) {
    test_thread(window);
    return SDL_CreateTextureFromSurface(window->renderer, surface);
}

void destroy_texture(struct window_t* window, SDL_Texture* texture) {
    test_thread(window);
    SDL_DestroyTexture(texture);
}

void set_background_color(struct window_t* window, SDL_Color color) {
    window->background = color;
}

font_id_t load_font(struct window_t* window, const char* fontname, int ptsize) {
    int fontid = 0;
    while (fontid < window->fontreg_size && window->loaded_fonts[fontid] != NULL) {
        fontid++;
    }

    if (fontid >= window->fontreg_size) {
        TTF_Font** tmp = (TTF_Font**)realloc(window->loaded_fonts, window->fontreg_size * 2);
        if (tmp == NULL) {
            return -1;
        }
        fontid = window->fontreg_size;
        window->fontreg_size *= 2;
        window->loaded_fonts = tmp;
    }

    TTF_Font* font = TTF_OpenFont(fontname, ptsize);
    if (font == NULL) {
        fontid = -1;
    } else {
        window->loaded_fonts[fontid] = font;
    }

    return fontid;
}

void render_copy(struct window_t* window, SDL_Texture* texture, const SDL_Rect* srcrect, const SDL_Rect* dstrect) {
    test_thread(window);
    SDL_RenderCopy(window->renderer, texture, srcrect, dstrect);
}

void render_surface(struct window_t* window, SDL_Surface* surface, const SDL_Rect* srcrect, const SDL_Rect* dstrect) {
    if (window == NULL || window->renderer == NULL || surface == NULL) {
        return;
    }
    test_thread(window);
    SDL_Texture* texture = SDL_CreateTextureFromSurface(window->renderer, surface);
    SDL_RenderCopy(window->renderer, texture, srcrect, dstrect);
    SDL_DestroyTexture(texture);
}

void render_set_color(struct window_t* window, SDL_Color color) {
    test_thread(window);
    SDL_SetRenderDrawColor(window->renderer, color.r, color.g, color.b, color.a);
}

void render_line(struct window_t* window, int x1, int y1, int x2, int y2, SDL_Color color) {
    test_thread(window);
    aalineRGBA(window->renderer, x1, y1, x2, y2, color.r, color.g, color.b, color.a);
}

void render_line_thick(struct window_t* window, int x1, int y1, int x2, int y2, int thickness, SDL_Color color) {
    test_thread(window);
    thickLineRGBA(window->renderer, x1, y1, x2, y2, thickness, color.r, color.g, color.b, color.a);
}

/**
 * Calcule les coordonnées des points lattéraux de la tête de flèche.
 * @param ex abscisse de la pointe
 * @param ey ordonnée de la pointe
 * @param dx direction X de la pointe (devrait être unitaire)
 * @param dy direction Y de la pointe (devrait être unitaire)
 * @param alpha angle de la flèche
 * @param size taille de la flèche
 * @param sx1 [out] abscisse de la première coordonnée lattérale
 * @param sy1 [out] ordonnée de la première coordonnée lattérale
 * @param sx2 [out] abscisse de la seconde coordonnée lattérale
 * @param sy2 [out] ordonnée de la seconde coordonnée lattérale
 */
static void arrow_sides(int ex, int ey, float dx, float dy, float alpha, float size, int* sx1, int* sy1, int* sx2, int* sy2) {
    double c = cos(alpha);
    double s = sin(alpha);
    *sx1 = ex + size * (dx * c - dy * s);
    *sy1 = ey + size * (dx * s + dy * c);
    *sx2 = ex + size * (dx * c + dy * s);
    *sy2 = ey + size * (-dx * s + dy * c);
}

void render_arrow(struct window_t* window, int x1, int y1, int x2, int y2, float size, float alpha, int thickness, SDL_Color color) {
    test_thread(window);

    int lx, ly, rx, ry;
    float length = NORM(x2 - x1, y2 - y1);
    arrow_sides(x2, y2, (float)(x1 - x2) / length, (float)(y1 - y2) / length, alpha, size,
            &lx, &ly, &rx, &ry);

    thickLineRGBA(window->renderer, x1, y1, x2, y2, thickness, color.r, color.g, color.b, color.a);
    thickLineRGBA(window->renderer, x2, y2, lx, ly, thickness, color.r, color.g, color.b, color.a);
    thickLineRGBA(window->renderer, x2, y2, rx, ry, thickness, color.r, color.g, color.b, color.a);
}

void render_arrow_curved(struct window_t* window, int x1, int y1, int x2, int y2, float size, float alpha, float curving, int diststart, int distend, SDL_Color color) {
    test_thread(window);

    float length = NORM(x2 - x1, y2 - y1);

    // Points de contrôlez pour la courbe de Bézier
    Sint16 xs[4], ys[4];
    xs[0] = x1; 
    ys[0] = y1;
    xs[1] = x1 + (x2 - x1) / 3.0 - curving * (y2 - y1) / length;
    ys[1] = y1 + (y2 - y1) / 3.0 + curving * (x2 - x1) / length;
    xs[2] = x2 - (x2 - x1) / 3.0 - curving * (y2 - y1) / length;
    ys[2] = y2 - (y2 - y1) / 3.0 + curving * (x2 - x1) / length;
    xs[3] = x2;
    ys[3] = y2;

    float n01 = NORM(xs[1] - xs[0], ys[1] - ys[0]);
    float n23 = NORM(xs[3] - xs[2], ys[3] - ys[2]);

    xs[0] += (diststart / n01) * (xs[1] - xs[0]);
    ys[0] += (diststart / n01) * (ys[1] - ys[0]);
    xs[3] += (distend / n23) * (xs[2] - xs[3]);
    ys[3] += (distend / n23) * (ys[2] - ys[3]);

    n23 = NORM(xs[3] - xs[2], ys[3] - ys[2]);
    
    // Arrow head
    int lx, ly, rx, ry;
    arrow_sides(xs[3], ys[3], 
            (float)(xs[2] - xs[3]) / n23, (float)(ys[2] - ys[3]) / n23, 
            alpha, size,
            &lx, &ly, &rx, &ry);

    bezierRGBA(window->renderer, xs, ys, 4, 2, color.r, color.g, color.b, color.a);
    aalineRGBA(window->renderer, xs[3], ys[3], lx, ly, color.r, color.g, color.b, color.a);
    aalineRGBA(window->renderer, xs[3], ys[3], rx, ry, color.r, color.g, color.b, color.a);
}


void render_rect(struct window_t* window, const SDL_Rect* rect, SDL_Color color) {
    test_thread(window);
    SDL_SetRenderDrawColor(window->renderer, color.r, color.g, color.b, color.a);
    SDL_RenderFillRect(window->renderer, rect);
}

void render_circle(struct window_t* window, int x, int y, int r, SDL_Color color) {
    test_thread(window);
    aacircleRGBA(window->renderer, x, y, r, color.r, color.g, color.b, color.a);
}

void render_text(struct window_t* window, const char* text, font_id_t fontid, int x, int y, int alignment, SDL_Color color, SDL_Color background) {
    test_thread(window);
    SDL_Surface* textsurf = TTF_RenderUTF8_Solid(window->loaded_fonts[fontid], text, color);
    SDL_Rect textarea;
    textarea.w = textsurf->w;
    textarea.h = textsurf->h;

    if ((alignment & 0x0F) == VALIGN_MIDDLE) {
        textarea.y = y - textarea.h / 2;
    } else if ((alignment & 0x0F) == VALIGN_TOP) {
        textarea.y = y;
    } else {
        textarea.y = y - textarea.h;
    }

    if ((alignment & 0xF0) == HALIGN_CENTER) {
        textarea.x = x - textarea.w / 2;
    } else if ((alignment & 0xF0) == HALIGN_LEFT) {
        textarea.x = x;
    } else {
        textarea.x = x - textarea.w;
    }

    SDL_SetRenderDrawColor(window->renderer, background.r, background.g, background.b, background.a);
    SDL_RenderFillRect(window->renderer, &textarea);

    SDL_Texture* texture = SDL_CreateTextureFromSurface(window->renderer, textsurf);
    SDL_RenderCopy(window->renderer, texture, NULL, &textarea);
    SDL_DestroyTexture(texture);
    SDL_FreeSurface(textsurf);
}



