% fonction maximisation_classification_MAP (pour l'exercice 3)

function [pourcentage_meilleur_classification_MAP, p1_max, ...
          vecteur_pourcentages_bonnes_classifications_MAP] = ...
         maximisation_classification_MAP(X,Y,valeurs_p1,mu_1,Sigma_1,mu_2,Sigma_2)

vecteur_pourcentages_bonnes_classifications_MAP =zeros(size(valeurs_p1),1);
    for i=1:size(valeurs_p1)
        vecteur_pourcentages_bonnes_classifications_MAP(i) = classification_MAP(X,valeurs_p1(i),mu_1,Sigma_1,mu_2,Sigma_2);
    end    
    p1_max=max(vecteur_pourcentages_bonnes_classifications_MAP);
    pourcentage_meilleur_classification_MAP=
end
