% fonction estim_param_MC_paire (pour exercice_2.m)

function parametres = estim_param_MC_paire(d,x,y_inf,y_sup)

p=size(x,1);

A_j = zeros(2*p,d-1);
for j=1:d-1
    A_j(:,j) = vecteur_bernstein(x,d-1,j);
    A_j(:,j) = vecteur_bernstein(x,d-1,j);
end

B_inf = y_inf-(1-x).^(d-1);
B_supp =y_sup-(1-x).^(d-1);

B_J= zeros(2*p,1);
B_J(1,:)=B_inf;
B_J(2,:)=B_supp;

parametres=A\B;


end
