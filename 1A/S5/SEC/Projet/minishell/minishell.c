#include <stdio.h>
#include <stdlib.h>
#include "readcmd.h"
#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>

void traitement(int numsign){
    printf("Le processus fils %d vient de se terminer\n", getpid());
}
    
    
int main(void) {
    struct sigaction action;
    action.sa_handler = traitement;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    sigaction(SIGCHLD,&action,NULL);

    bool fini= false;

    while (!fini) {
        printf("> ");
        struct cmdline *commande= readcmd();

        if (commande == NULL) {
            // commande == NULL -> erreur readcmd()
            perror("erreur lecture commande \n");
            exit(EXIT_FAILURE);
    
        } else {

            if (commande->err) {
                // commande->err != NULL -> commande->seq == NULL
                printf("erreur saisie de la commande : %s\n", commande->err);
        
            } else {

                /* Pour le moment le programme ne fait qu'afficher les commandes 
                   tapees et les affiche à l'écran. 
                   Cette partie est à modifier pour considérer l'exécution de ces
                   commandes 
                */
                int indexseq= 0;
                char **cmd;
                while ((cmd= commande->seq[indexseq])) {
                    if (cmd[0]) {
                        if (strcmp(cmd[0], "exit") == 0) {
                            fini= true;
                            printf("Au revoir ...\n");
                        }
                        else {
                            printf("commande : ");
                            int indexcmd= 0;
                            while (cmd[indexcmd]) {
                                printf("%s ", cmd[indexcmd]);
                                indexcmd++;
                            }
                            printf("\n");
                            int retour = fork();
                            if (retour == -1 ) {

                            }
                            else if (retour == 0) {

                                execvp(cmd[0],cmd);
                            }
                            else {
                                if (commande->backgrounded != NULL){
                                }
                                else{
                                    int status;
                                    int fils_fin = waitpid(-1, &status, WUNTRACED);
                                    if (WIFEXITED(status)){
                                        printf("%d arrété\n", fils_fin);
                                    }
                                    else if(WIFSIGNALED(status)){
                                        printf("%d tué\n", fils_fin);
                                    }
                                }
                            }
                            
                            
                        }

                        indexseq++;
                    }
                }
            }
        }
    }
    return EXIT_SUCCESS;
}