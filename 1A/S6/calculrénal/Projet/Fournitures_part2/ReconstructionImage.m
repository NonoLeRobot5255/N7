%%  Application de la SVD : compression d'imagesdiag(W)
clear alln_ev3
close all

% Lecture de l'image]=eig(M);
I = imread('BD_Asterix_1.png');
I = rgb2gray(I);
I = double(I);
[q, p] = size(I);

% Décomposition par SVD
fprintf('Décomposition en valeurs singulières\n')
tic
[U, S, V] = svd(I);
toc

l = min(p,q);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% On choisit de ne considérer que 200 vecteurs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% vecteur pour stocker la différence entre l'image et l'image reconstuitetime
inter = 1:40:(200+40);
inter(end) = 200;
differenceSVD = zeros(size(inter,2), 1);

% images reconstruites en utilisant de 1 à 200 vecteurs (avec un pas de 40)
ti = 0;
td = 0;
for k = inter

    % Calcul de l'image de rang k
    Im_k = U(:, 1:k)*S(1:k, 1:k)*V(:, 1:k)';

    % Affichage de l'image reconstruite
    ti = ti+1;
    figure(ti)
    colormap('gray')
    imagesc(Im_k), axis equal
    
    % Calcul de la différence entre les 2 images
    td = td + 1;
    differenceSVD(td) = sqrt(sum(sum((I-Im_k).^2)));
end

% Figure des différences entre image réelle et image reconstruite
ti = ti+1;
figure(ti)
hold on 
plot(inter, differenceSVD, 'rx')
ylabel('RMSE')
xlabel('rank k')



% Plugger les différentes méthodes : eig, puissance itérée et les 4 versions de la "subspace iteration method" 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% QUELQUES VALEURS PAR DÉFAUT DE PARAMÈTRES, 
% VALEURS QUE VOUS POUVEZ/DEVEZ FAIRE ÉVOLUER
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% tolérance
eps = 1e-9;
% nombre d'itérations max pour atteindre la convergence
maxit = 10000;

% taille de l'espace de recherche (m)
search_space = 400;

% pourcentage que l'on se fixe
percentage = 0.995;

% p pour les versions 2 et 3 (attention p déjà utilisé comme taille)
puiss =3;

%%%%%%%%%%%%%
% À COMPLÉTER
%%%%%%%%%%%%%

%vérification des dimensions de I
tourner = (p > q);
if (tourner)
    I= I';
    [q,p]=size(I);
end
M=I*I';

fonction=5;

%%
% calcul des couples propres
switch fonction
    case 0 %eig
        [Vp,diag_vp]=eig(M);
    case 1 %powerv12
         [ Vp, diag_vp, m, ~, ~ ] = power_v11( M, search_space, percentage, eps, maxit );
    case 2 %subspaceiterv0
        [Vp,diag_vp,m,~]= subspace_iter_v0(M, search_space, eps, maxit);
    case 3 %subspaceiterv1
        [Vp,diag_vp, m, ~, ~, ~ ] = subspace_iter_v1( M, search_space, percentage, eps, maxit );
    case 4 %subspaceiterv2
        [Vp,diag_vp, m, ~, ~, ~ ] = subspace_iter_v2( M, search_space, percentage, puiss, eps, maxit );
    case 5 %subspaceiterv3
        [Vp,diag_vp, m, ~, ~, ~ ] = subspace_iter_v3( M, search_space, percentage, puiss, eps, maxit );
end

[vp_trie,indices]=sort(diag(diag_vp),'descend');
Vp_trie=Vp(:,indices);
%%
% calcul des valeurs singulières
vp_sing=diag(sqrt(vp_trie(1:m)));
Vp_sing=Vp_trie(:,1:m);

%%
% calcul de l'autre ensemble de vecteurs
%%
Vp_autre=zeros(p,m);
for j=1:m
    Vp_autre(:,j)=(I'*Vp_sing(:,j))/vp_sing(j,j);
end



% images reconstruites en utilisant de 1 à 200 vecteurs (avec un pas de 40)
td = 0;
if(tourner)
    I=I';
end
inter_vpk=1:round((m/10)):m;
% calcul des meilleures approximations de rang faible
differenceSVD_postcompr = zeros(size(inter_vpk,2), 1);
for k = inter_vpk

    % Calcul de l'image de rang k
    Im_k = Vp_sing(:, 1:k)*vp_sing(1:k, 1:k)*Vp_autre(:, 1:k)';
    if(tourner)
        Im_k=Im_k';
    end
    % Affichage de l'image reconstruite
    ti = ti+1;
    figure(ti)
    colormap('gray')
    imagesc(Im_k), axis equal
    
    % Calcul de la différence entre les 2 images
    td = td + 1;
    differenceSVD_postcompr(td) = sqrt(sum(sum((I-Im_k).^2)));
end

% Figure des différences entre image réelle et image reconstruite
ti = ti+1;
figure(ti)
hold on 
plot(inter_vpk, differenceSVD_postcompr, 'rx')
ylabel('RMSE')
xlabel('rank k')
%%
