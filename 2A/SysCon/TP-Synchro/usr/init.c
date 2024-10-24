/**
 * @file usr/init.c
 * @brief L'init du monde utilisateur
 * 
 * Attention, ici les include sont dans usr/include !!!
 */
#include <manux/config.h>
#include <manux/types.h>
#include <stdio.h>
#include <unistd.h>

#include <manux/i386.h> // halt

void calculerPremiers(int q)
/*
 * Calcul et affichage des nombres premiers. Le but est juste de faire
 * bosser le processeur, donc on ne cherche pas du tout à faire les
 * choses vite ou bien.
 */
{
   int n; /* Indice de la boucle de recherche d'un premier*/
   int d; /* Indice de la boucle de recherche de diviseur */
   booleen compose;
   int cpt = 1;
   int nbLu;
   
   char txt[32];
   
   while (TRUE) {
      printf("[%d] C'est la boucle numero %d : \n", q, cpt++);
      printf("%d", 2);
      for (n = 3; n < 512; n += 2) {
         compose = FALSE;
         d = 3;
         while ((!compose) && (d*d <= n)) {
	    compose = compose || (n%d == 0);
            d += 2;
         }
         if (!compose) {
            printf(", %d", n); for (int i = 0; i<10000000; i+=2){asm("");};
	 }
      }
      printf("\n--------------------------------------------------------------------------------\n");

      // Test du clavier et stdin
      nbLu = lire(0, txt, 31);
      if (nbLu) {
	 txt[nbLu] = 0;
         printf("   Lu %d => '%s'\n", nbLu, txt);
      }

#ifndef MANUX_PREEMPTIF
      basculerTache();
#endif
   }
}

void deuxiemeTache()
{
   int n;
   
   printf("Deuxieme tache\n");
   
   for (n = 0; n < 10000000; n++) {
      calculerPremiers(2);
   }
}

void init()
{
   int n=2; // nombre de messages affichés

   printf("Greetings from userland !\n");
   
   n = creerNouvelleTache(deuxiemeTache, FALSE);

   for (n = 0; n < 10000000; n++) {
      calculerPremiers(1);
   }
}
