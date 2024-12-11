%% on efface tout et set les variables
clear all;
close all;

nb_bits = 2000;

%% tracé du treillis 
trellis = poly2trellis(3,[5 7]);
commcnv_plotnextstates(trellis.outputs);

%% code convolutif 
% signal crée
S = randi([0 1],1,nb_bits);

% codage canal
code_codage=convenc(S,trellis);

matrice_comparaison = [S ones(size(S))*2 ; code_codage];

% code sorti

code_decode = vitdec(code_codage,trellis,5*(3-1),'term','hard');

mat = (S~=code_decode);
TEB = mean(mat)