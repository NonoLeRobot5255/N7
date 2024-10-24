% fonction modelisation_vraisemblance (pour l'exercice 1)

function modele_V = modelisation_vraisemblance(X,mu,Sigma)

modele_V=zeros(size(X,1),1);
inverse=inv(Sigma);

for i=1:size(X,1)

    
    expo = -(1/2) * (X(i,:)-mu) * inverse * (X(i,:)-mu)';

    modele_V(i) =  exp(expo);
end 
denum = 2 * pi * sqrt(det(Sigma));
modele_V = modele_V /denum;
end