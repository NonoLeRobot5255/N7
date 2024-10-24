% fonction classification_MAP (pour l'exercice 3)

function Y_pred_MAP = classification_MAP(X,p1,mu_1,Sigma_1,mu_2,Sigma_2)
colonne1=modelisation_vraisemblance(X,mu_1,Sigma_1);
colonne2=modelisation_vraisemblance(X,mu_2,Sigma_2);

colonnes=zeros(size(X,1),2);
colonnes(:,1)=colonne1*p1;
colonnes(:,2)=colonne2*(1-p1);

[~,Y_pred_MAP]=max(colonnes,[],2);

    
end
