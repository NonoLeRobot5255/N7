%on ferme tout 
clear all;
close all;

%% variables 
N = 16;
N_actif = 16;
nb_bits = 1000;



%% figure de zinzin
figure('Name','porteuse 1 et 4 actives')
     %% modulateur 
        
    
        % Mapping
        S=zeros(N, nb_bits);
        for i=1:N_actif
            S(i,:) = randi([0 1],1,nb_bits)*2 -1;
        end 
 
        
    
    
        % filtrage
        Xe = ifft(S,N);
        Y = reshape(Xe, 1, nb_bits*N);
    
        %dsp
        dsp = pwelch(Y,[],[],[],16,'centered'); % on utilise la fréquence pour centrer correctement pwelch
        
        %tracé
        
        nexttile
        plot(10*log(dsp))
        xlabel('fréquence')
        ylabel('dsp')

     %% Démodulation 
     
     %démodulation
     Y_reshape = reshape(Y, size(Xe));
     Y_recep = fft(Y_reshape,N);
     Y_recep = sign(Y_recep);
    
     
     %TEB
     TEB = mean(S~=Y_recep,"all");