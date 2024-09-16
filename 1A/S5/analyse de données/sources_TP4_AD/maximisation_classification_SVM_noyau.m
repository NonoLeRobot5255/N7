% fonction maximisation_classification_SVM_noyau (pour l'exercice 2)

function [pourcentage_meilleur_classification_SVM_test, sigma_opt_test, ...
          vecteur_pourcentages_bonnes_classifications_SVM_app, ...
          vecteur_pourcentages_bonnes_classifications_SVM_test] = ...
          maximisation_classification_SVM_noyau(X_app,Y_app,X_test,Y_test,vecteur_sigma)

for i=1:length(vecteur_sigma)
    sigma=vecteur_sigma(i);
    [X_VS,Y_VS,alpha_VS,c,code_retour]=estim_param_SVM_noyau(X_app,Y_app,sigma);
    if code_retour ~=1
        break
    end
    

end