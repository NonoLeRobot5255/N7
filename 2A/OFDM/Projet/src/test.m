%on ferme tout 
clear all;
close all;

%% variables 
N = 16;           % nombre de porteuses
N_actif = 16;     % nombre de porteuses actives
nb_bits = 1000;   % nombre de bits
EbN0dB = [0:6];   % gamme d'Eb/N0 en dB
EbN0 = 10.^(EbN0dB./10);  % conversion d'Eb/N0 en linéaire
taille_garde = 2; % taille du préfixe cyclique

%% figure de zinzin
figure('Name', 'porteuse 1 et 4 actives')

%% modulateur
% Mapping des bits à moduler
S = zeros(N, nb_bits);
for i = 1:N_actif
    S(i, :) = randi([0 1], 1, nb_bits) * 2 - 1;  % Bits en -1 ou +1
end

% Filtrage : IFFT pour chaque porteuse
Xe = ifft(S, N);  % IFFT des porteuses
intervalle = Xe(N - taille_garde + 1:end, :);  % ajout du préfixe cyclique
Xe = [intervalle; Xe];  % préfixe + signal

% Reshape du signal pour la transmission
Y = reshape(Xe, 1, nb_bits * (N + taille_garde));
Px = mean(abs(Y).^2);  % puissance du signal

for i = 1:length(EbN0dB)
    % Calcul du bruit
    sigma2 = Px / (2 * log2(4) * EbN0(i));  % bruit pour chaque Eb/N0
    recu = Y + sqrt(sigma2);  % réception du signal bruité
    
    %% Démodulation
    demodule = recu .* cos(2 * pi * [0:length(recu)-1]) - 1i * recu .* sin(2 * pi * [0:length(recu)-1]);  % démodulation
    Y_reshape = reshape(demodule, size(Xe));  % reshape pour avoir la même forme
    Xs = Y_reshape(taille_garde + 1:N + taille_garde, :);  % enlever le préfixe cyclique
    Y_recep = fft(Xs, N);  % FFT pour récupérer les symboles
    z = reshape(Y_recep, 1, []);  % mettre z sous forme de vecteur ligne
    
    % Initialisation de xr de la même taille que z
    xr = zeros(1, length(z));
    
    % Remplissage de xr avec les bits décodés : on prend la partie réelle et imaginaire
    xr(1:2:length(z)) = real(z) < 0;  % pour les indices impairs : partie réelle
    xr(2:2:length(z)) = imag(z) < 0;  % pour les indices pairs : partie imaginaire
    
    % Calcul du TEB (en comparant tous les bits)
    TEB(i) = mean(S(:) ~= xr);  % comparer chaque bit dans S et xr
end

% TEB final
TEB_final = mean(S(:) ~= reshape(Y_recep, 1, []), "all");
