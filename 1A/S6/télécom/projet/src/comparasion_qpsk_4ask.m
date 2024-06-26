clear all;
close all;

% QPSK

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=2;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 90000 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 6;
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception


for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    dk = 1-2*S(1:2:nb_bits) +1i * (1-2*S(2:2:nb_bits));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % Filtrage
    % Echelle temporelle
    
    y = filter(h1, 1, At);
    T1 = ([0:length(y)-1] * Te);
   
    %bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));
    
    recu=y+sqrt(sigma2)*randn(1,length(y));
    recu = recu  + 1i *sqrt(sigma2)*randn(1,length(y));
    
    
    %filtre de récéption
    z= filter(hr,1,recu);

    
    %echantillonage et démapping 
    xe = z(length(h1):Ns:length(z)-1);
    
    xr(1:2:nb_bits)=real(xe)<0;
    xr(2:2:nb_bits)=imag(xe)<0;
    
    TEB (k) = mean(S ~= xr);
end
figure
% TEB QPSK
semilogy(EbN0dB,TEB);
hold on

% 4-ASK

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=2;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 10000;
S = randi([0 1],nb_bits,1);
L= 6;
Ns = Fe *Ts; % Nombre d'échantillons par bits
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception

EbN0dB = [0:6];
EbN0= 10.^(EbN0dB./10);
TEB = zeros(1,length(EbN0));
for i=1:size(EbN0,2)

%% modulateur :
% Mapping
n=2;
M=2^2;


S2 = reshape(S',2,nb_bits/2);
S2E = [1, nb_bits/2];
Choix = [-3 -1; 3 1];
for j=1:size(S2,2)
    S2E(j) = Choix(S2(1,j)+1,S2(2,j)+1);
end
At = [kron(S2E, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];

% Filtrage
T1 = 0:Te:(nb_bits*Ns-1)*Te/2; % Echelle temporelle
y2 = filter(h1, 1, At);



%bruit 
Px = mean(abs(y2).^2);
sigma2 = (Px * Ns)/(2*log2(M)*EbN0(i));
bruit = sqrt(sigma2) * randn(1, length(y2));
recu = y2+bruit;

% filtre de récéption
z = filter(hr,1,recu);

%echantillonage et démapping
xe = z(length(h1):Ns:length(z)-1);

xr_temp = zeros(1,length(S)/2);
xr_temp(xe>2)=3;
xr_temp(xe<=2 & xe>0)=1;
xr_temp(xe<=0 & xe>-2)=-1;
xr_temp(xe<=-2)=-3;

xr = [];
for j=1:length(S)/2
    if xr_temp(j)== -3
        xr = [xr 0 0];
    elseif xr_temp(j)== -1
        xr = [xr 0 1];
    elseif xr_temp(j)== 1
        xr = [xr 1 1];
    else
        xr = [xr 1 0];
    end
    
end

TEB(i) = mean(S' ~= xr);
end


% TEB 4-ASK
semilogy(EbN0dB,TEB)
legend('QPSK','4-ASK')
xlabel('Eb/N0')
ylabel('TEB')

figure('Name','DSP')
%DSP QPSK
DSP1 = pwelch(y, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP1));
semilogy(axe_frequences,fftshift(DSP1))
xlabel('Fréquence (Hz)');
ylabel('DSP');
title('tracé de la DSP par rapport a la fréquence');
hold on
%DSP 4-ASK
DSP2 = pwelch(y2, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP2));
semilogy(axe_frequences,fftshift(DSP2))
legend('QPSK','4-ASK')