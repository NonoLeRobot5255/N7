#include <stdio.h>
#include <unistd.h>

//on veut lire une série d'entier depuis le pipe dans le fils et les afficher
int main() {
    int buffer[100]; 
    int message[] = {1, 2, 45, 4, 5, 6,-1};
    int tube[2];
    if (pipe(tube) == -1){
        printf("Erreur lors de la création du tube\n");
        return 1;
    }
    int fils = fork();
    if (fils == -1){
    }
    else if (fils ==0){
        close(tube[1]);
        int x;
        x = read(tube[0],buffer,sizeof(buffer));
        for (int i = 0; i < x; i++) {
            if (buffer[i]<=0){
                break;
            }
            else{
                printf("%d\n", buffer[i]);
            }
        }
        printf("sortie de boucle\n");
    }
    else{
        close(tube[0]);
        write(tube[1], message, sizeof(message));
        sleep(10);
    }
}