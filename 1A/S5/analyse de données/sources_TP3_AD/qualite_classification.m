% fonction qualite_classification (pour l'exercice 2)

function [pourcentage_bonnes_classifications_total,pourcentage_bonnes_classifications_fibrome, ...
          pourcentage_bonnes_classifications_melanome] = qualite_classification(Y_pred,Y)

pourcentage_bonnes_classifications_fibrome = sum(Y==1 & Y_pred == 1)/sum(Y==1)*100;
pourcentage_bonnes_classifications_melanome= sum(Y~=1 & Y_pred ~= 1)/sum(Y~=1)*100;
pourcentage_bonnes_classifications_total = (pourcentage_bonnes_classifications_melanome + pourcentage_bonnes_classifications_fibrome)/2;


end