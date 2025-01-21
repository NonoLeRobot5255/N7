%% on efface tout et set les variables
clear all;
close all;

nb_bits = 2000;

%% tracé du treillis 
trellis = poly2trellis(3,[5 7]);
commcnv_plotnextstates(trellis.outputs);

%% code convolutif 
% signal crée
S = randi([0 1],1,nb_bits) ;
Sbis= [S zeros(1,2)];

% codage canal
code_codage=convenc(S,trellis);

code_codage1 = 1 - 2 * code_codage ;





% code sorti

code_soft = vitdec(code_codage,trellis,5*(3-1),'trunc','soft',1);
code_hard = vitdec(code_codage,trellis,5*(3-1),'trunc','hard');
code_unquant = vitdec(code_codage1,trellis,5*(3-1),'trunc','unquant');

mat1 = (S~=code_soft);
mat2 = (S~=code_hard);
mat3 = (S~=code_unquant);

TEB_soft = mean(mat1);
TEB_hard = mean(mat2);
TEB_unquant = mean(mat3);