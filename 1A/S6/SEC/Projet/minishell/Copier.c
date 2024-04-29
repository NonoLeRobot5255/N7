#include <stdio.h>
#include <stdlib.h>
#include "readcmd.h"
#include <stdbool.h>
#include <string.h>

#include <fcntl.h>



int copier(int argc,char* argv[]) {
    int retour;

    # define BUFSIZE 1024
    char tampon [BUFSIZE];
    int lus;
    int ecrits;


    if (argc != 3) {
        printf("nombre d'argumet incorrect");
        exit(-1);
    }
    int src = open(argv[1],O_RDONLY);   
    if (src == -1) {
        printf("erreur lors de l'ouverture du fichier source");
        exit(-1);
    }
    int dst = open(argv[2],O_WRONLY|O_CREAT|O_TRUNC, 0666);
    if (dst == -1) {
        printf("erreur lors de l'ouverture du fichier destination");
        exit(-1);
    }
    while ((lus = read(src,tampon, BUFSIZE)) > 0) {
        ecrits = write(dst,tampon,lus);
        if (ecrits == -1) {
            printf("erreur lors de l'écriture");
            exit(-1);
        }
    }
    close(src);
    close(dst);
    return EXIT_SUCCESS;

}