% function ACP (pour exercice_2.m)

function [C,bornes_C,coefficients_RVG2gris] = ACP(X)
X_c = X-mean(X);
Sigma =  (X_c' * X_c)/size(X, 1);
[W,D] = eig(Sigma);
[~,indice]=sort(diag(D),"descend");
W=W(:,indice);
C=X_c*W;
bornes_C=[min(C(:,1)) min(C(:,2)) min(C(:,3))];
coefficients_RVG2gris=0;

    
end
