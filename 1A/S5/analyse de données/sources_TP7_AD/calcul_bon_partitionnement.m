% fonction calcul_bon_partitionnement (pour l'exercice 1)

function meilleur_pourcentage_partitionnement = calcul_bon_partitionnement(Y_pred,Y)

classes = [1 2 3];
classes = perms(classes);

meilleur_pourcentage_partitionnement = 0;

for i=1:length(classes)
    Y_bis = classes(i,:)';
    
    for j=1:3 
        p=unique(Y);
        p_classe = (sum(Y== p(j) & Y_pred==Y_bis(j))/sum(Y==p(j)))*100;
    end
    meilleur_pourcentage_partitionnement = max(meilleur_pourcentage_partitionnement,p_classe);
end
end