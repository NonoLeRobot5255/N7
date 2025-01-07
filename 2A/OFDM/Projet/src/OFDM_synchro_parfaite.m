%on ferme tout 
clear all;
close all;

%% variables 
N = 16;
N_actif = 16;
nb_bits_porteuse = 10000;
nb_bits = nb_bits_porteuse * N;
garde = 6;
synchro = 3;

% réponse impultionelle du filtre
h = [0.407,0.815,0.407]; 

%egalisation 
ck = fft(h,16);
matr_ck = repmat(ck(:), 1, nb_bits_porteuse);
H = 1./matr_ck;

%% Réponse du canal
% tracé du module et de la phase de la réponse en fréquence du canal de propagation.
freqz(h,1,16,16,'whole')
title('Réponse en fréquence du canal de propagation');
grid on


%% figure pour représenter les porteuses actives
figure('Name','dsp en sortie de canal')
     %% modulateur 
        
    
        % Mapping
        S=zeros(N, nb_bits_porteuse);
        for i=1:N_actif
            S(i,:) = randi([0 1],1,nb_bits_porteuse)*2 -1;
        end 
       
    
    
        % modulation 
        Signal_module = ifft(S,N);

        %% Intervalle de garde
        Prefixe = Signal_module(N-garde+1:end,:);
        Signal_garde = [Prefixe;Signal_module];

        % signal en ligne
        Signal_sortie = reshape(Signal_garde, 1, nb_bits+garde*nb_bits_porteuse);

        % canal
        Signal_sortie_canal = filter(h,1,Signal_sortie);         
            
        %dsp
        [dsp,f] = pwelch(Signal_sortie_canal,[],[],[],16); % on utilise la fréquence pour centrer correctement pwelch
        
        %tracé de la DSP
        
        nexttile
        plot(f,10*log(dsp))
        xlabel('fréquence')
        ylabel('dsp')
        grid on

     %% Démodulation 
     
     %supression de l'intervalle de garde
     Signal_matrice_canal = reshape(Signal_sortie_canal, size(Signal_garde));
     signal_echantilloner = Signal_matrice_canal(synchro+1:N+synchro,:);

     %fft en sortie pour revenir a un signal binaire comparable 
     bit_fin = fft(signal_echantilloner,N);
     
     %%Egalisation
     bit_parfait = bit_fin.*H;

     %constellation porteuse 6 et 15 (ok)
     porteuse6 = bit_parfait(6, :);
     porteuse15 = bit_parfait(15, :);


     figure('Name','constellation porteuse 6')
     scatter(real(porteuse6), imag(porteuse6))
     xlabel('partie réel')
     ylabel('partie imaginaire')


     figure('Name','constellation porteuse 15')
     scatter(real(porteuse15), imag(porteuse15))
     xlabel('partie réel')
     ylabel('partie imaginaire')


     %on choisit +1 ou -1 afin de prédire
     Signal_recep = real(bit_parfait)>0;
     Signal_recep = Signal_recep*2-1;
    
     
     %TEB
     TEB = mean(S~=Signal_recep,"all")