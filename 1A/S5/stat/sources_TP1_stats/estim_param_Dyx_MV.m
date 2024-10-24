% Fonction estim_param_Dyx_MV (exercice_1.m)

function [a_Dyx,b_Dyx,residus_Dyx] = ...
           estim_param_Dyx_MV(x_donnees_bruitees,y_donnees_bruitees,tirages_psi)
[x_g,y_g, x_c,y_c] = centrage_des_donnees(x_donnees_bruitees,y_donnees_bruitees);

residus_Dyx = (y_c - x_c * tan(tirages_psi)).^2 ;
[~,indice] = min(sum(residus_Dyx));
a_Dyx=tan(tirages_psi(indice));
b_Dyx=y_g-x_g*a_Dyx;
residus_Dyx= y_donnees_bruitees - a_Dyx * x_donnees_bruitees +b_Dyx;
end