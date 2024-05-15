#include <stdio.h>
#include <unistd.h>

// Création d'un tube, dans un fils, le père écrit dans le tube et le fils lit dans le tube
int main(){
    char buffer[100]; 
    char message[] = "123456789"; 
    int fils = fork();
    if (fils == -1){
    }
    else if (fils == 0){
        close(tube[1]);
        read(tube[0], buffer, 100);
        printf("Message lu par le fils : %s\n", buffer);
    }
    else{
        int tube[2];
        if (pipe(tube) == -1){
            printf("Erreur lors de la création du tube\n");
            return 1;
        }
        // Ecriture dans le tube
        close(tube[0]);
        write(tube[1], message, sizeof(message));
    }
    
}