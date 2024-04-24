#include <stdio.h>
#include <stdlib.h>
#include "readcmd.h"
#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>



int nbcmd = 0;
void traitement(int numsign){
    int status;
    int pid = waitpid(-1, &status, WNOHANG);
    if (pid > 0){
        printf("%d done\n", pid);
    }
    nbcmd--;  
}
    
    
int main(void) {
    
    struct sigaction action;
    action.sa_handler = waitpid;
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
                                
                                if (commande->backgrounded != NULL){ // si la commande est en background
                                    nbcmd++;
                                    printf("[%d] %d\n",nbcmd, retour);
                                    signal(SIGCHLD, traitement);   
                                    WEXITSTATUS(retour);
                                                                                               
                                }
                                else{
                                    nbcmd++;
                                    waitpid(retour, NULL, 0);                                    
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