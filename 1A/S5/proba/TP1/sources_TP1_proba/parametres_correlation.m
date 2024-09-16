% Fonction parametres_correlation (exercice_1.m)

function [r,a,b] = parametres_correlation(Vd,Vg)
somme_x=mean(Vd);
ecart_x=mean(Vd.^2 - somme_x^2);
ecart_x=sqrt(ecart_x);

somme_y=mean(Vg);
ecart_y=mean(Vg.^2 - somme_y^2);
ecart_y=sqrt(ecart_y);

cov=mean((Vg.*Vd)-mean(Vd)*mean(Vg));

r=cov/(ecart_x * ecart_y);
a=cov/(ecart_x^2);
b=mean(somme_y)-mean(Vd)*cov/(ecart_x^2);

end