function [A, D, info] = matgen_csad(imat, n)

info = 0;
D = zeros(n,1);
A = zeros(n,n);

switch imat
    case 1
        % imat == 1
        
        cond = n;
        
        for i = 1:n
            D(i) = n-i+1;
        end
        
        A = full(sprandsym(n, 1., D));
        
    case 2
        % imat == 2
        
        cond = 1e10;
        alpha = log(1/cond);
        
        for i = 1:n
            D(i) = exp(alpha*rand(1));
        end
        
        A = full(sprandsym(n, 1., D));
        
    case 3
        % imat == 3
        
        cond = 1e5;
        alpha = cond^(-1/(n-1));
        
        for i = 1:n
            D(i) = alpha^(i-1);
        end
        
        A = full(sprandsym(n, 1., D));
        
    case 4
        % imat == 4
        
        cond = 1e2;
        temp = 1/cond;
        alpha = (1-temp)/(n-1);
        
        for i = 1:n
            D(i) = (n-i)*alpha + temp;
        end
        
        A = full(sprandsym(n, 1., D));
        
    otherwise
        info = -1;
        
end

D = sort(D, 'descend');

%% vérification
% [W,V] = eig(A);
% V = sort(diag(V), 'descend')

% norm(D-V)/norm(D)

end
