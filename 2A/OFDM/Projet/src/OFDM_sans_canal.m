%on ferme tout 
clear all;
close all;

%% variables 
N = 16;
N_actif = 16;
nb_bits_porteuse = 10000;
nb_bits = nb_bits_porteuse * N;


%% figure pour représenter les porteuses actives
figure('Name','dsp en fonction du nombre de porteuses actives')
     %% modulateur 
        
    
        % Mapping
        S=zeros(N, nb_bits_porteuse);
        for i=1:N_actif
            S(i,:) = randi([0 1],1,nb_bits_porteuse)*2 -1;
        end 
       
    
    
        % modulation
        Signal_module = ifft(S,N);
        Signal_sortie = reshape(Signal_module, 1, nb_bits);
    
        %dsp
        [dsp,f] = pwelch(Signal_sortie,[],[],[],16,'centered'); % on utilise la fréquence pour centrer correctement pwelch
        
        %tracé
        
        nexttile
        plot(f,10*log(dsp))
        xlabel('fréquence')
        ylabel('dsp')

     %% Démodulation 
     
     %démodulation
     Signal_en_ligne = reshape(Signal_sortie, size(Signal_module));
     %fft en sortie pour revenir a un signal binaire comparable 
     bit_fin = fft(Signal_en_ligne,N);
     %on choisit +1 ou -1 affin de prédire
     bit_fin = sign(bit_fin);
    
     
     %TEB
     TEB = mean(S~=bit_fin,"all")