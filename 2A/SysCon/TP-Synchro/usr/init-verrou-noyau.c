/**
 * @file usr/init.c
 * @brief L'init du monde utilisateur
 * 
 * Attention, ici les include sont dans usr/include !!!
 */
#include <manux/types.h>
#include <stdio.h>
#include <manux/errno.h>
#include <unistd.h>   // creerNouvelleTache
#include <manux/string.h>

void uneActiviteQuelconque()
{
   for (int n = 0; n < 10; n++) {
      appelSystemeInutile();
      printf("[%d]\n", n);
   }
}

void init()
{

   printf("Sympa le mode utilisateur !\n");
   
   for (int n = 0 ; n < 2; n++){
      creerNouvelleTache(uneActiviteQuelconque, FALSE);
   }
   while(1){};
}
