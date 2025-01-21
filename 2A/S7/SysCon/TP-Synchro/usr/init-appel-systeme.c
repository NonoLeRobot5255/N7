/**
 * @file usr/init.c
 * @brief L'init du monde utilisateur
 * 
 * Attention, ici les include sont dans usr/include !!!
 */
#include <manux/types.h>
#include <stdio.h>
#include <unistd.h>   // creerNouvelleTache

void init()
{
   int r = 1;

   printf("Sympa le mode utilisateur !\n");

   r = appelSystemeInutile();
   
   printf("r = %d\n", r);

}
