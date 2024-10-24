% Fonction estim_param_Dyx_MC2 (exercice_2bis.m)

function [a_Dyx,b_Dyx,coeff_r2] = ...
                   estim_param_Dyx_MC2(x_donnees_bruitees,y_donnees_bruitees)
[x_g,y_g,x_c,y_c] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees);

var_x = mean(x_donnees_bruitees.^2)-mean(x_donnees_bruitees)^2;
var_y = mean(y_donnees_bruitees.^2)-mean(y_donnees_bruitees)^2;

cov_xy = mean(x_c .* y_c);

coeff_r2 = cov_xy^2;
r = (cov_xy)/sqrt(var_x* var_y);

a_Dyx = r * sqrt(var_y/ var_x);
b_Dyx = y_g - a_Dyx * x_g;

end