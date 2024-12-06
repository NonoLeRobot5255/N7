function porteeEulerien(G)
% PORTEEEULERIEN Cette fonction détermine les portées (distances) pour lesquelles
% un graphe donné par la matrice d'adjacence G est eulérien. Elle vérifie pour chaque
% distance unique, si le graphe est eulérien en construisant une matrice d'adjacence
% modifiée pour cette portée et en utilisant la fonction isEulerian pour tester.
% Elle affiche ensuite un graphique montrant à quelles portées le graphe est eulérien
% et imprime ces distances.

% Détermination de la taille de la matrice G
[m,n] = size(G);

% Tests de robustesse optionnels : vérifier que la matrice est carrée et symétrique
assert(n == m, 'La matrice d''entrée doit être carrée');
assert(isequal(G, G'), 'La matrice d''entrée doit être symétrique');

% Remplacement des éléments de la diagonale principale par Inf
G(logical(eye(n))) = Inf;

% Remodeler la matrice en vecteur et trier ses valeurs
O = sort(reshape(G, 1, m * n));
% Filtrer pour obtenir toutes les distances uniques supérieures à 0 et non infinies
D = unique(O(O < Inf));

% Allouer un vecteur pour tracer les résultats
eulerien = ones(size(D));

% Vecteur pour stocker les portées où le graphe est eulérien
eulerian_distances = [];

% Boucle sur chaque distance unique pour vérifier si le graphe est eulérien à cette portée
for i = 1:size(D, 2)
    A = G <= D(i); % Créer une matrice d'adjacence pour les arêtes inférieures ou égales à D(i)
    is_eulerian = isEulerian(A); % Vérifier si le graphe est eulérien
    eulerien(i) = is_eulerian; % Stocker le résultat
    if is_eulerian
        eulerian_distances(end + 1) = D(i); % Enregistrer la distance si le graphe est eulérien
    end
end

% Création d'une nouvelle figure pour le graphique
figure;
plot(D, eulerien, '-x'); % Tracer le graphique des résultats
set(gca, 'YTick', 0:2); % Définir les marques sur l'axe des Y
axis([0 D(end) 0 2]); % Définir les limites des axes
title('Pour quelle portée le graphe est-il eulérien? (en incluant la valeur de la portée)');

% Imprimer toutes les distances pour lesquelles le graphe est eulérien
fprintf('Portées pour lesquelles le graphe est eulérien (en incluant la valeur de la portée):\n');
fprintf('%d\n', eulerian_distances);
end

