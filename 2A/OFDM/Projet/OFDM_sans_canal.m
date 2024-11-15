%on ferme tout 
clear all;
close all;

%% variables 
N = 16;
N_actif = 1;
nb_bits = 1000;

S=zeros(N, nb_bits);
%% modulateur 

    % Mapping
    for i=1:N_actif
        S(i,:) = randi([0 1],1,nb_bits)*2 -1;
    end    
    


    % filtrage
    Xe = ifft(S,N);
    Y = reshape(Xe, 1, nb_bits*N);

    %dsp
    dsp = pwelch(Y,[],[],[],16,'center'); % on utilise la fréquence pour centrer correctement pwelch

    %tracé
    figure('Name','dsp')
    nexttile
    plot(10*log(dsp))
    xlabel('fréquence')
    ylabel('')