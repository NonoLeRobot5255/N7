% fonction entrainement_foret (pour l'exercice 2)

function foret = entrainement_foret(X,Y,nb_arbres,proportion_individus)
        nb_individus=proportion_individus *length(Y);
        foret = cell(nb_arbres);
        for i=1:nb_arbres
            indice = randperm(length(Y),nb_individus);
            X_pred=X(indice,:);
            Y_pred=Y(indice,:);
            foret{i} = fitctree(X_pred,Y_pred,NumVariablesToSample=round(sqrt(size(X,2))));

        end 
        
end
