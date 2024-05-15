#include <stdio.h>
#include <stdlib.h>
#include "readcmd.h"
#include <stdbool.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <unistd.h>


int pid_fg=0;
int nbcmd = 0;
void traitement(int numsign){
    int status;
    int pid = waitpid(-1, &status, WNOHANG);
    if (WIFEXITED(status)){
        printf("\nprocessus %d terminé\n", pid);
        pid_fg = 0;
    }
    else if (WIFSIGNALED(status)){
    }
    else if (WIFSTOPPED(status)){
    }
    else if (WIFCONTINUED(status)){
    }
    else{
        pid_fg = 0;
        printf("%d done\n", pid_fg);
    }
}
void traitementc (int numsign){
    if (pid_fg == 0){
        printf("\nAucun processus en cours\n");
    }
    else {
        printf ("\nprocessus %d tué\n", pid_fg);
        kill(pid_fg, SIGKILL);
        pid_fg = 0;
    }
    
}
void traitementz (int numsign){
    if (pid_fg == 0){
        printf("\nAucun processus en cours\n");
    }
    else {
        printf("\nprocessus %d stoppé manuellement\n", pid_fg);
        kill(pid_fg, SIGSTOP); 
        pid_fg = 0;
    }
}
    
    
int main(void) {
    char buffer[100]; 
    
    int tubeE[2];
    int tubeL[2];
    if (pipe(tubeE) == -1){
        printf("Erreur lors de la création du tube\n");
        return 1;
    }
    if (pipe(tubeL) == -1){
        printf("Erreur lors de la création du tube\n");
        return 1;
    }
    
    struct sigaction action;
    action.sa_handler = traitement;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    sigaction(SIGCHLD,&action,NULL);

    struct sigaction actionc;
    actionc.sa_handler = traitementc;
    sigemptyset(&actionc.sa_mask);
    actionc.sa_flags = SA_RESTART;
    sigaction(SIGINT,&actionc,NULL);

    struct sigaction actionz;
    actionz.sa_handler = traitementz;
    sigemptyset(&actionz.sa_mask);
    actionz.sa_flags = SA_RESTART;
    sigaction(SIGTSTP,&actionz,NULL);


    bool fini = false;

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
                            fini = true;
                            printf("Au revoir ...\n");
                        }
                        else {
                            if(commande->seq[indexseq-1] && commande->seq[indexseq-1][0]){
                                close(tubeL[1]);
                                dup2(tubeL[0], 0);
                                close(tubeL[0]);                      
                            }
                            if(commande->seq[indexseq+1] && commande->seq[indexseq+1][0]){
                                close(tubeE[0]); 
                                dup2(tubeE[1], 1);
                                close(tubeE[1]);                       
                            }
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
                                setpgrp();
                                if (commande->in != NULL){
                                    int fd = open(commande->in, O_RDONLY);
                                    dup2(fd, 0);
                                    close(fd);
                                }
                                if (commande->out != NULL){
                                    int fd = open(commande->out, O_WRONLY|O_CREAT|O_TRUNC, 0666);
                                    dup2(fd, 1);
                                    close(fd);
                                }
                                execvp(cmd[0],cmd);
                            }
                            else {
                                sigaction(SIGINT, &actionc, NULL);
                                sigaction(SIGTSTP, &actionz, NULL);
                                sigaction(SIGCHLD, &action, NULL); 
                                if (commande->backgrounded != NULL){ // si la commande est en background
                                    nbcmd++;
                                    printf("[%d] %d\n",nbcmd, retour);                                                              
                                }
                                else{
                                    pid_fg = retour;
                                     while (pid_fg != 0)
                                     {
                                        pause();
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