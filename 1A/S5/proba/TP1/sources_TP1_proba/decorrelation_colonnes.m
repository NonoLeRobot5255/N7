% Fonction decorrelation_colonnes (exercice_2.m) 

function I_decorrelee = decorrelation_colonnes(I)
I_decorrelee=I;
I_decorrelee(:,2:end)=I_decorrelee(:, 2:end)-I_decorrelee(:,1:end-1);

end