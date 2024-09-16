% fonction estim_param_SVM_noyau (pour l'exercice 2)

function [X_VS,Y_VS,Alpha_VS,c,code_retour] = estim_param_SVM_noyau(X,Y,sigma)
G=ones(size(X));
n=length(X);
for i=1:n 
    for j=1:n 
        G(i,j)=exp(-sum((X(i,:)-X(j,:)).^2)/(2*sigma^2));
    end
end
H = diag(Y)* G*diag(Y);
f = -ones(length(Y),1);
Aeq = Y' ;
beq = 0 ;
lb =zeros(size(Y));

[alpha,~,code_retour]=quadprog(H,f,[],[],Aeq,beq,lb,[]);

I_VS=(alpha>1e-6);

X_VS = X(I_VS,:);
Y_VS = Y(I_VS,:);
Alpha_VS = alpha(I_VS,:);


c = G *diag(Y_VS)*Alpha_VS;




end
