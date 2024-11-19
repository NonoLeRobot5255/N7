%on utilise freqz pour ça 
%on ferme tout 
clear all;
close all;

% réponse impultionelle 
h = [0.407,0.815,0.407];
%% tracé du module et de la phase de la réponse en fréquence du canal de propagation.
freqz(h,1,1024,'whole')
title('Réponse en fréquence du canal de propagation');
xlabel('Fréquence (rad/échantillon)');
ylabel('Amplitude et Phase');
grid on;


%% variables 
N = 16;
N_actif = 16;
nb_bits = 1000;



%% figure de zinzin
figure('Name','DSP')
     %% modulateur 


        % Mapping
        S=zeros(N, nb_bits);
        for i=1:N_actif
            S(i,:) = randi([0 1],1,nb_bits)*2 -1;
        end 




        %% Canal
        Xe = ifft(S,N);
        Y = reshape(Xe, 1, nb_bits*N);


        %filtre 
        SignalSortieCanal=filter(h,1,Y) ;

        %dsp
        
        [pxx, f] = pwelch(SignalSortieCanal, [], [], [], 16); % pxx = DSP, f = fréquence
        dsp_normalisee = pxx*16 / sum(pxx); % Normalisation entre 0 et 16
        nexttile
        plot(10*log(dsp_normalisee))
        xlabel('fréquence')
        ylabel('dsp')
     %% Démodulation 

     %démodulation
     Y_reshape = reshape(SignalSortieCanal, size(Xe));
     Y_recep = fft(Y_reshape,N);
        
     %constellation porteuse 6 et 15 (ok)
     porteuse6 = Y_recep(6, :);
     porteuse15 = Y_recep(15, :);


     figure('Name','constellation porteuse 6')
     scatter(real(porteuse6), imag(porteuse6))
     xlabel('partie réel')
     ylabel('partie imaginaire')


     figure('Name','constellation porteuse 15')
     scatter(real(porteuse15), imag(porteuse15))
     xlabel('partie réel')
     ylabel('partie imaginaire')
     


     %% TEB
     Y_fin = [];
     for i=1:length(Y_recep)
        if real(Y_recep)>0
            Y_fin = [Y_fin 1];
        else
            Y_fin= [Y_fin -1];
        end
     end
     TEB = mean(S~=Y_fin,"all")