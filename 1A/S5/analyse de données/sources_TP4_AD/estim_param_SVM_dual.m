% fonction estim_param_SVM_dual (pour l'exercice 1)

function [X_VS,w,c,code_retour] = estim_param_SVM_dual(X,Y)
H = diag(Y)* (X*X')*diag(Y);

f = -ones(length(Y),1);
Aeq = Y' ;
beq = 0 ;
lb =zeros(size(Y));

[alpha,~,code_retour]=quadprog(H,f,[],[],Aeq,beq,lb,[]);

I_VS=(alpha>1e-6);

X_VS = X(I_VS,:);
Y_VS = Y(I_VS,:);
alpha_VS = alpha(I_VS,:);

w = X_VS'*diag(Y_VS)*alpha_VS;

c=w'*X_VS(1,:)'-Y_VS(1);

end
