% fonction classification_MV (pour l'exercice 2)

function Y_pred_MV = classification_MV(X,mu_1,Sigma_1,mu_2,Sigma_2)

colonne1=modelisation_vraisemblance(X,mu_1,Sigma_1);
colonne2=modelisation_vraisemblance(X,mu_2,Sigma_2);

colonnes=zeros(size(X,1),2);
colonnes(:,1)=colonne1;
colonnes(:,2)=colonne2;

[~,Y_pred_MV]=max(colonnes,[],2);

end
