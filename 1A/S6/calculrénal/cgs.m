%--------------------------------------------------------------------------
% ENSEEIHT - 1SN - Calcul scientifique
% TP1 - Orthogonalisation de Gram-Schmidt
% cgs.m
%--------------------------------------------------------------------------

function Q = cgs(A)

    % Recuperation du nombre de colonnes de A
    [~, m] = size(A);
    
    % Initialisation de la matrice Q avec la matrice A
    Q = A;
    
    %------------------------------------------------
    % A remplir
    % Algorithme de Gram-Schmidt classique
    %------------------------------------------------
    Q(:,1)=A(:,1)/sqrt(A(:,1)'*A(:,1));
    for i=2:m
        y = A(:,i);
        composante = (Q(:,1:i-1)'*y)'.*Q(:,1:i-1);
        y = y-sum(composante,2);
        y = y/sqrt(y'*y);
        Q(:,i)=y;
    end
end