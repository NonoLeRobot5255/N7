clear all;
close all;

%QPSK

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=2;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 9000 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 6;
h1 = rcosdesign(0.35,L,Ns); % Reponse impulsionnelle du filtre
hr = fliplr(h1);


for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    dk = 1-2*S(1:2:nb_bits) +1i * (1-2*S(2:2:nb_bits));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % Filtre
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
semilogy(EbN0dB,TEB,'bp');
hold on

%8-PSK

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=3;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 9000 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 8;
h1 = rcosdesign(0.2,L,Ns); % Reponse impulsionnelle du filtre
hr = fliplr(h1);


for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    S3 = reshape(S',3,nb_bits/3);
    S3E = [1, nb_bits/3];
    Choix = [0 3;1 2];
    Choix(:,:,2) = [7 4;6 5];
    for j=1:size(S3,2)
        S3E(j) = Choix(S3(1,j)+1,S3(2,j)+1,S3(3,j)+1);
    end
    dk = pskmod(S3E,8,pi/8,'gray');

    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % Filtre
    % Echelle temporelle
    
    y2 = filter(h1, 1, At);
    T1 = ([0:length(y2)-1] * Te);
   
    %bruit
    Px = mean(abs(y2).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));
    
    recu=y2+sqrt(sigma2)*randn(1,length(y2));
    recu = recu  + 1i *sqrt(sigma2)*randn(1,length(y2));
    
    
    %filtre de récéption
    z= filter(hr,1,recu);

    
    %echantillonage et démapping 
    xe = z(length(h1):Ns:length(z)-1);
        
    xr_temp = pskdemod(xe,8,pi/8,'gray');
    xr = [];
    for j=1:length(S)/3
        if xr_temp(j)== 0
            xr = [xr 0 0 0];
        elseif xr_temp(j)== 1
            xr = [xr 1 0 0];
        elseif xr_temp(j)== 2
            xr = [xr 1 1 0];
        elseif xr_temp(j)== 3
            xr = [xr 0 1 0];
        elseif xr_temp(j)== 4
            xr = [xr 0 1 1];
        elseif xr_temp(j)== 5
            xr = [xr 1 1 1];
        elseif xr_temp(j)== 6
            xr = [xr 1 0 1];
        else
            xr = [xr 0 0 1];
        end
    end

    TEB (k) = mean(S ~= xr);
end

%TEB simulé
semilogy(EbN0dB,TEB,'rp')
legend('QPSK','8-PSK')

figure('Name','DSP')
DSP1 = pwelch(y, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP1));
semilogy(axe_frequences,fftshift(DSP1))
xlabel('Fréquence (Hz)');
ylabel('DSP');
title('tracé de la DSP par rapport a la fréquence');
hold on
DSP2 = pwelch(y2, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP2));
semilogy(axe_frequences,fftshift(DSP2))
legend('QPSK','8-PSK')