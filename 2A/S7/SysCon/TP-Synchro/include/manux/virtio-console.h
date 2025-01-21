/**
 * @file virtio-console.h
 * @brief Définition des éléments de base des consoles virtio
 *
 */
#ifndef VIRTIO_CONSOLE_DEF
#define VIRTIO_CONSOLE_DEF

#include <manux/virtio.h>
#include <manux/periph-car.h>

/**
 * Les features négociables
 */
#define VIRTIO_CONSOLE_F_SIZE      0x01
#define VIRTIO_CONSOLE_F_MULTIPORT 0x02

/**
 * Les numéros des files. Pour le moment, on n'en gère qu'un !
 */
#define VIRTIO_CONSOLE_PORT0_IN   0
#define VIRTIO_CONSOLE_PORT0_OUT  1

/**
 * Cette fonction va voir si quelquechose est dispo
 * Elle doit sûrement disparaître, mais je vais tenter de faire un
 * peu de polling
 */
void virtioConsoleTraiterBuffers();

/**
 * @brief Initialisation des périphériques
 */
int virtioConsoleInitialisation(INoeud * iNoeudVirtioConsole);

#endif
