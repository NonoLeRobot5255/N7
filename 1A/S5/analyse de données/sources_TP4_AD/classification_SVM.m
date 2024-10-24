% fonction classification_SVM (pour l'exercice 1)

function Y_pred = classification_SVM(X,w,c)
n=length(X);
Y_pred=zeros(n,1);
for i=1:n
    Y_pred(i)=sign(w'*X(i,:)'-c);
end


end