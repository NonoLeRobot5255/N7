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
void traitement(int numsign) {
    int status;
    int pid;
    
    while ((pid = waitpid(-1, &status, WNOHANG)) > 0) { // on récupère le pid du processus qui s'est terminé
        nbcmd--;
        if (WIFEXITED(status)) {
            printf("\nprocessus %d terminé normalement\n", pid);
        } else if (WIFSIGNALED(status)) {
            
        } else if (WIFSTOPPED(status)) {
            
        }

        if (pid == pid_fg) {
            pid_fg = 0;
        }
    }
}
void traitementc (int numsign){
    if (pid_fg == 0){
        printf("\nAucun processus en avant plan\n");
        
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
        printf("\nprocessus %d mis en pause\n", pid_fg);
        kill(pid_fg, SIGSTOP); 
        pid_fg = 0;
    }
}
    
    
int main(void) {
    // on crée une structure sigaction pour traiter les signaux
    struct sigaction action;
    action.sa_handler = traitement;
    sigemptyset(&action.sa_mask);
    action.sa_flags = SA_RESTART;
    sigaction(SIGCHLD,&action,NULL);

    // on crée une structure sigaction pour traiter le signal controle C
    struct sigaction actionc;
    actionc.sa_handler = traitementc;
    sigemptyset(&actionc.sa_mask);
    actionc.sa_flags = SA_RESTART;
    sigaction(SIGINT,&actionc,NULL);

    // on crée une structure sigaction pour traiter le signal controle Z
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
                // création des tubes
                int tubeE[2];
                int tubeL[2];
                // création du buffer
                char buffer[1024]; 
                
                char **cmd;
                pipe(tubeL);
                while ((cmd= commande->seq[indexseq])) {
                    // on copie nos contenus de tubeL dans tubeE
                    tubeE[0] = tubeL[0];
                    tubeE[1] = tubeL[1];
                    // on crée un nouveau pipe pour la sortie
                    pipe(tubeL);
                    // on ferme le tube d'ecriture
                    close(tubeE[1]);  
                    if (cmd[0]) {
                        if (strcmp(cmd[0], "exit") == 0) {
                            fini = true;
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
                            // on crée un processus fils
                            int retour = fork();
                            if (retour == -1 ) { // erreur, on ne fait rien

                            }
                            else if (retour == 0) { // on est dans le fils
                                setpgrp(); // on change le groupe du fils
                                if ((indexseq == 0) && (commande -> seq[indexseq+1]== NULL)){ // si on a une seule commande
                                    if (commande->in != NULL){  // si on a un fichier en entrée   
                                    int fd = open(commande->in, O_RDONLY);
                                    dup2(fd, 0);
                                    close(fd);
                                    }
                                    if (commande->out != NULL){ // si on a un fichier en sortie
                                        int fd = open(commande->out, O_WRONLY|O_CREAT|O_TRUNC, 0666);
                                        dup2(fd, 1);
                                        close(fd);
                                    }
                                }
                                else if (  indexseq == 0  ){    // si on a plusieurs commandes et qu'on est sur la première
                                    if (commande -> in != NULL){    // si on a un fichier en entrée
                                        int fd = open(commande -> in , O_RDONLY);
                                        dup2(fd, 0);
                                        close(fd);
                                        
                                    }
                                    dup2(tubeL[1], 1); // on redirige la sortie standard vers le tube
                                    
                                }
                                else if (commande -> seq[indexseq+1] == NULL){ // si on est sur la dernière commande
                                    if (commande -> out != NULL){ // si on a un fichier en sortie
                                        int fd = open(commande -> out, O_WRONLY|O_CREAT|O_TRUNC, 0666);
                                        dup2(fd, 1);
                                        close(fd);
                                    }
                                    dup2(tubeE[0], 0); // on redirige l'entrée standard vers le tube
                                }
                                else { // si on est dans une commande intermédiaire
                                    // on redirige l'entrée standard vers le tube
                                    // on redirige la sortie standard vers le tube
                                    dup2(tubeL[1], 1);
                                    dup2(tubeE[0], 0);
                                }
                                // on ferme les tubes
                                close(tubeE[0]);
                                close(tubeE[1]);
                                close(tubeL[0]);
                                close(tubeL[1]);
                                // on execute la commande
                                execvp(cmd[0],cmd);
                                // si on arrive ici, c'est qu'il y a eu une erreur on termine le processus
                                exit(EXIT_FAILURE);
                            }
                            else { // on est dans le père
                                sigaction(SIGINT, &actionc, NULL);
                                sigaction(SIGTSTP, &actionz, NULL);
                                sigaction(SIGCHLD, &action, NULL); 
                                if (commande->backgrounded != NULL){ // si la commande est en background
                                    nbcmd++;
                                    printf("[%d] %d\n",nbcmd, retour);                                                              
                                }
                                else{ // si la commande est en avant plan
                                    nbcmd ++;
                                    pid_fg = retour;
                                     while (pid_fg != 0)
                                     {
                                        // on attend la fin du processus et on ne récupère la main que si le processus est terminé
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