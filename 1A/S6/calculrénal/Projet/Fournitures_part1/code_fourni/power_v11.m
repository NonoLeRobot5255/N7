% méthode de la puissance itérée avec déflation

% Données
% A          : matrice dont on cherche des couples propres
% m          : nombre maximum de valeurs propres que l'on veut calculer
% percentage : pourcentage recherché de la trace
% eps        : seuil pour déterminer si un couple propre a convergé (méthode de la puissance itérée)
% maxit      : nombre maximum d'itérations pour calculer une valeur propre (méthode de la puissance itérée)

% Résultats
% V : matrice des vecteurs propres
% D : matrice diagonale contenant les valeurs propres (ordre décroissant)
% n_ev : nombre de couples propres calculés
% itv : nombre d'itérations pour chaque couple propre
% flag : indicateur sur la terminaison de l'algorithme
%  flag = 0  : on a convergé (on a calculé le pourcentage voulu de la trace)
%  flag = 1  : on a atteint le nombre maximum de valeurs propres sans avoir atteint le pourcentage
%  flag = -3 : on n'a pas convergé en maxit itérations pour calculer une valeur propre
function [ V, D, n_ev, itv, flag ] = power_v11( A, m, percentage, eps, maxit )
    
    n = size(A,1);

    % initialisation des résultats
    W = [];
    V = [];
    itv = [];
    n_ev = 0;

    % trace de A
    tA = trace(A);
 
    % somme des valeurs propres
    eig_sum = 0.0;

    % indicateur de la convergence (pourcentage atteint)
    convg = 0;
    
    % numéro du couple propre courant
    k = 0;

    while (~convg && k < m)
        
        k = k + 1;

        % méthode de la puissance itérée
        v = randn(n,1);
        z = A*v;
        beta = v'*z;

        % conv = || beta * v - A*v||/|beta| < eps
        % voir section 2.1.2 du sujet
        norme = norm(beta*v - z, 2)/norm(beta,2);
        nb_it = 1;
        
        while(norme > eps && nb_it < maxit)
          y = A*v;
          v = y / norm(y,2);
          z = A*v;
          beta = v'*z;
          norme = norm(beta*v - z, 2)/norm(beta,2);
          nb_it = nb_it + 1;
        end
        
        % la calcul de ce couple propre a échoué => échec global
        if(nb_it == maxit)
          flag = -3;
          D = 0;
          % on sort de la fonction en plein milieu
          % ce n'est pas très bien structuré
          % pardon aux enseignants de PIM
          return;
        end
        
        % on sauvegarde le couple propre
        W(k) = beta;
        V(:,k) = v;
        itv(k) = nb_it;
        eig_sum = eig_sum + beta;

        % déflation
        A = A - beta * (v*v');

        % est-ce qu'on a atteint le pourcentage
        convg = eig_sum/tA > percentage;
        
    end

    % on a atteint le pourcentage
    if (convg)
      n_ev = k;
      flag = 0;
      W = W';
      D = diag(W);
    else
      % ce n'est pas le cas
      flag = 1;
      D = 0;
    end
    
end
