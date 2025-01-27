clear all;
close all;

%% QPSK bande de base

%% Constantes
Rb = 84.4 * 10^6; % Débit binaire en bits par seconde
Fe = Rb; % Fréquence d'échantillonnage 
Te = 1 / Fe; % Période d'échantillonnage
Tb = 1 / Rb; % Durée d'un bit
n = 2; % Nombre de bits par symbole
M = 2^n; % Ordre de la modulation 

Ts = log2(M) * Tb; % Durée d'un symbole
Rs = Rb / log2(M); % Débit symbole
nb_bits = 100000; % Nombre total de bits à simuler
Ns = Fe * Ts; % Nombre d'échantillons par symbole

EbN0dB = [-4:0.5:4];% Rapport signal sur bruit en dB
EbN0 = 10.^(EbN0dB / 10); % Rapport signal sur bruit linéaire
L = 8; % Longueur du filtre en nombre de symboles
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception

%% CHAINE DE TRANSMISSION
for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    dk = 1-2*S(1:2:nb_bits) +1i * (1-2*S(2:2:nb_bits));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    %% canal 
    % Filtrage de mise en forme
    
    y = filter(h1, 1, At);
    T1 = ([0:length(y)-1] * Te);
   
    % Ajout de bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));
    
    y_et_bruit_reel = y + sqrt(sigma2)*randn(1,length(y)); % bruit réel
    recu = y_et_bruit_reel + 1i *sqrt(sigma2)*randn(1,length(y)); % bruit imaginaire
    
    
    % Filtre de récéption
    z= filter(hr,1,recu);

    
    % Echantillonage et démapping 
    xe = z(length(h1):Ns:length(z)-1);
    xr(1:2:nb_bits)=real(xe)<0;
    xr(2:2:nb_bits)=imag(xe)<0;
    
    % Calcul du TEB
    TEB(k) = mean(S ~= xr);
end

%% Trace des courbes
figure
%TEB simulé bande de base
semilogy(EbN0dB,TEB)
xlabel('Eb/N0 (dB)')
ylabel('TEB')
hold on
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'g')
grid on


%% PRECISION
Ne=0;
EbN0dB = 10;
EbN0 = 10*log10(EbN0dB);
k=0;
while Ne<4
    k=k+1;
    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    dk = 1-2*S(1:2:nb_bits) +1i * (1-2*S(2:2:nb_bits));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];

    %% canal 
    % Filtrage de mise en forme

    y = filter(h1, 1, At);
    T1 = ([0:length(y)-1] * Te);

    % Ajout de bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0));

    y_et_bruit_reel = y + sqrt(sigma2)*randn(1,length(y)); % bruit réel
    recu = y_et_bruit_reel + 1i *sqrt(sigma2)*randn(1,length(y)); % bruit imaginaire


    % Filtre de récéption
    z= filter(hr,1,recu);


    % Echantillonage et démapping 
    xe = z(length(h1):Ns:length(z)-1);
    xr(1:2:nb_bits)=real(xe)<0;
    xr(2:2:nb_bits)=imag(xe)<0;

    Ne = Ne+sum(S ~= xr);
end

prec = (1/Ne)^0.5;
TEB_precision = Ne/(k*10000);