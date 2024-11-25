%on ferme tout 
clear all;
close all;

%% variables 
N = 16;
N_actif = 16;
nb_bits = 10000;
EbN0dB = [0:0.01:8];
EbN0=10.^(EbN0dB./10);
taille_garde=2;
M=4;
%% figure de zinzin
figure('Name','porteuse 1 et 4 actives')
     %% modulateur 
        
    
        % Mapping
        S=zeros(N, nb_bits);
        for i=1:N_actif
            S1 = randi([0 1],1,nb_bits*2);
            S(i,:) = 1-2*S1(1:2:nb_bits*2) +1i * (1-2*S1(2:2:nb_bits*2));
        end 
        S_ligne = reshape(S,1,[]);
        S_bits = zeros(1, 2 * length(S_ligne));
        S_bits(1:2:end) = real(S_ligne) < 0; % Bits sur I
        S_bits(2:2:end) = imag(S_ligne') < 0; % Bits sur Q 
        
    
    
        % filtrage
        Xe = ifft(S,N);
        intervalle = Xe(N-taille_garde+1:end,:);
        Xe = [intervalle;Xe];
        Y = reshape(Xe, 1, nb_bits*(N+taille_garde));
        Px = mean(abs(Y).^2);
        for i=1:length(EbN0dB)
            sigma2 = ((Px )/(2*log2(4)*EbN0(i)));
            bruit = sqrt(sigma2) .* randn(1,length(Y));
            recu=Y+bruit;
            %% Démodulation 
            %démodulation
            Y_reshape = reshape(recu,size(Xe));
            Xs = Y_reshape(taille_garde+1:end,:);
            Y_recep = fft(Xs,N);
            z= reshape(Y_recep,1,[]);
            z_bits = zeros(1, 2 * length(z));
            z_bits(1:2:end) = real(z) < 0; % Bits sur I
            z_bits(2:2:end) = imag(z) > 0; % Bits sur Q
            TEB(i) = mean(S_bits ~= z_bits);
            
            
        end
        TEB_th = 2*qfunc(sqrt(2*log2(M)*10.^(EbN0dB/10))*sin(pi/M))/log2(M);
        semilogy(EbN0dB,TEB)
        hold on 
        semilogy(EbN0dB,TEB_th)