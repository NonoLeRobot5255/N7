%on ferme tout 
clear all;
close all;

%% variables 
N = 16;
N_actif = 1;
nb_bits_porteuse = 1000;
nb_bits = nb_bits_porteuse * N;


%% figure pour représenter les porteuses actives
figure('Name','dsp en fonction du nombre de porteuses actives')
     %% modulateur 
        
    
        % Mapping
        S=zeros(N, nb_bits_porteuse);
        for i=1:N_actif
            S(i,:) = randi([0 1],1,nb_bits_porteuse)*2 -1;
        end 
 
        
    
    
        % filtrage
        Signal_filtre = ifft(S,N);
        Signal_sortie = reshape(Signal_filtre, 1, nb_bits);
    
        %dsp
        dsp = pwelch(Signal_sortie,[],[],[],16,'centered'); % on utilise la fréquence pour centrer correctement pwelch
        
        %tracé
        
        nexttile
        plot(10*log(dsp))
        xlabel('fréquence')
        ylabel('dsp')

     %% Démodulation 
     
     %démodulation
     Signal_en_ligne = reshape(Signal_sortie, size(Signal_filtre));
     bit_fin = fft(Signal_en_ligne,N);
     bit_fin = sign(bit_fin);
    
     
     %TEB
     TEB = mean(S~=bit_fin,"all");