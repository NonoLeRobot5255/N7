/**
 * @file virtio-net.h
 */
#ifndef VIRTIO_NET_DEF
#define VIRTIO_NET_DEF

#include <manux/virtio.h>
/**
 * @brief Initialisation des périphériques
 */
int virtioNetInit();

void virtioNetTestDeuxiemeEmission();
void virtioReseauPoll();

#endif
