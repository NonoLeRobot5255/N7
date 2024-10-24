% Fonction estim_param_Dyx_MC1 (exercice_2.m)

function [a_Dyx,b_Dyx,coeff_R2] = ...
                   estim_param_Dyx_MC1(x_donnees_bruitees,y_donnees_bruitees)
 A = zeros(size(x_donnees_bruitees,1),2);
A (:,1) = x_donnees_bruitees ;  
A (:,2) = ones(size(x_donnees_bruitees,1),1);

B = y_donnees_bruitees;

X = ((A'*A) \A') * B;

a_Dyx = X(1);
b_Dyx = X(2);
donne_centre = y_donnees_bruitees - mean(y_donnees_bruitees);
coeff_R2 = 1 - (sum((y_donnees_bruitees - a_Dyx * x_donnees_bruitees - b_Dyx).^2))/(sum(donne_centre.^2));

    
end