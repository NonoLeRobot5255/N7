function chain_exists = possedechaine(Adj, c)
    % POSSEDECHAINE Vérifie si une chaîne est présente dans le graphe
    % G est la matrice d'adjacence
    % c est le vecteur représentant la chaîne
    % La fonction retourne true si la chaîne est présente, sinon false

    % Nombre de nœuds dans la chaîne
    n = length(c);
    
    % Initialisation de la variable de retour
    chain_exists = true;
    
    % Boucle pour vérifier chaque paire de nœuds dans la chaîne
    for i = 1:(n-1)
        % Si il n'y a pas d'arête entre deux nœuds consécutifs, la chaîne n'existe pas
        if Adj(c(i), c(i+1)) == 0
            chain_exists = false;
            break;
        end
    end
end

