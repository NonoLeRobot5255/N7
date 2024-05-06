function [q, qv] = verification_qualite(A, D, W, V, n)

q = zeros(n,1);

for i = 1:n
    q(i) = norm(D(i) - W(i))/norm(D(i));
end

% qualité de chaque couple propre
qv = zeros(n,1);
for i = 1:n
    qv(i) = norm(A*V(:,i) - W(i)*V(:,i))/norm(W(i));
end

end