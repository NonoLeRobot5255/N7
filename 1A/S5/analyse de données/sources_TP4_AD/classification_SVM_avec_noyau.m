% fonction classification_SVM_avec_noyau (pour l'exercice 2)

function Y_pred = classification_SVM_avec_noyau(X,sigma,X_VS,Y_VS,Alpha_VS,c)
G=ones(size(X));
n=length(X);
for i=1:n 
    for j=1:n 
        G(i,j)=exp(-sum((X_VS(i,:).^2-X_VS(j,:).^2))/(2*sigma^2));
    end
end

n=length(X);
Y_pred=zeros(n,1);
for i=1:n
    Y_pred(i)=sign(Alpha_VS(i,:)*Y_VS(i,:)*G(i,:)-c);
end



end