%%%%% SET ENV %%%%%
clear all;
close all;

addpath('matlab_bgl');      %load graph libraries
addpath('matlab_tpgraphe'); %load tp ressources

load TPgraphe.mat;          %load data

%%%%%% DISPLAY INPUT DATA ON TERMINAL %%%%%

cities %names of cities
D      %distance matrix bw cities
pos    %x-y pos of the cities

%%%%%%EXO 1 (modeliser et afficher le graphe) %%%%%
A=(D<500); %adj matrix


viz_adj(D,A,pos,cities);

viz_adj(D,graphPower(A,2),pos,cities);

viz_adj(D,graphPower(A,3),pos,cities);

viz_adj(D,graphPower(A,10),pos,cities);

viz_adj(D,graphPower(A,12),pos,cities);



%%%%%% EXO 2 %%%%%

%Q1 - existence d'un chemin de longueur 3
A3 = graphPower(A,3) - graphPower(A,2);
viz_adj(D, A3,pos,cities);

%Q2 - nb de chemins de 3 sauts
nb3 = sum(sum(A3))/2;

%Q3 - nb de chemins <=3
A3_sans_diag = graphPower(A,3)-eye(size(A));
nb3_inf = sum(sum(A3_sans_diag))/2;

%%%%%%%% EXO 3 %%%%%
c=[18 13 9]; %la chaine 18 13 9 est t dans le graphe?
possedechaine(A,c)
c=[18 6 3]; %la chaine 18 6 3 est t dans le graphe?
possedechaine(A,c)
c=[26 5 17]; %la chaine 26 5 17 est t dans le graphe?
possedechaine(A,c)

%%%%%%%% EXO 4%%%%%
isEulerien(A)

%%%%%%%% EXO 5%%%%%
porteeEulerien(D)
