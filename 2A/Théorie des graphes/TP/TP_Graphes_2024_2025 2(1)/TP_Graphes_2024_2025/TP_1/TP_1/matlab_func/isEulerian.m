function is_eulerian = isEulerian(adjMatrix)
    % IS_EULERIAN vérifie si un graphe déjà connecté est eulérien
    % Selon le théorème d'Euler, un graphe est eulérien si tous les sommets ont un degré pair.
    
    % On vérifie la connexité pour les sommets reliés par des arrêtes
    if ~verifierConnexite(adjMatrix)
        is_eulerian = false; % Affecter la valeur false à is_eulerian
        return;              % Quitter la fonction
    end

    % Compter le nombre de sommets de degré impair
    nb_impairs = sum(mod(sum(adjMatrix, 2), 2) == 1);

    % Vérifier si au plus 2 sommets ont un degré impair
    is_eulerian = nb_impairs < 3;
end

function estConnexe = verifierConnexite(G)
    % Cette fonction vérifie si un graphe est connexe
    % Entrée:
    %   G : une matrice d'adjacence du graphe
    % Sortie:
    %   estConnexe : un booléen (true ou false)
    
    % Nombre de sommets dans le graphe
    n = size(G, 1);
    degres = sum(G, 2);

    % Filtrer les sommets avec au moins une arête
    sommets_actifs = find(degres > 0);

    % Initialisation de la liste des sommets visités
    visite = false(1, n);
    
    % Démarrage de la visite par le premier sommet actif, s'il existe
    if isempty(sommets_actifs)
        estConnexe = true; % Un graphe sans arêtes est trivialement connexe
        return;
    end
    queue = sommets_actifs(1);
    visite(queue) = true;

    while ~isempty(queue)
        current = queue(1);
        queue(1) = [];
        
        % Trouver tous les sommets non visités adjacents à 'current'
        for i = sommets_actifs'
            if G(current, i) == 1 && ~visite(i)
                visite(i) = true;
                queue(end+1) = i;  % Ajout du sommet à la queue
            end
        end
    end
    
    % Le graphe est connexe si tous les sommets actifs ont été visités
    estConnexe = all(visite(sommets_actifs));
end
