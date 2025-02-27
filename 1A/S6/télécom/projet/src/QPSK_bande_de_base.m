clear all;
close all;

% QPSK bande de base

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=2;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 10000 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 8;
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception

figure('Name','constellations')

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
    
    y_et_bruit_reel = y + sqrt(sigma2)*randn(1,length(y)); % bruit réel
    recu = y_et_bruit_reel + 1i *sqrt(sigma2)*randn(1,length(y)); % bruit imaginaire
    
    
    %filtre de récéption
    z= filter(hr,1,recu);

    
    %echantillonage et démapping 
    xe = z(length(h1):Ns:length(z)-1);

    %tracé de la constellation
    titre = EbN0dB(k);
    nexttile
    plot(real(xe),imag(xe),'linestyle','none','marker','o')
    grid on
    xlabel('partie réel')
    ylabel('partie imaginaire')
    title(['Eb/N0 = ' num2str(titre) ])
    
    
    xr(1:2:nb_bits)=real(xe)<0;
    xr(2:2:nb_bits)=imag(xe)<0;
    
    TEB (k) = mean(S ~= xr);
end

figure
%TEB simulé bande de base
semilogy(EbN0dB,TEB)
hold on 

% QPSK frequence porteuse

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 8;
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception
fp = 2000;

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
    
    
    %porteuse
    p = real(y) .*cos(2*pi*fp*T1) - imag(y) .*sin(2*pi*fp*T1);
    
    %bruit
    Px = mean(abs(p).^2);
    sigma2 = ((Px * Ns)/(2*log2(M)*EbN0(k)));
    
    recu=p+sqrt(sigma2)*randn(1,length(y));
    
    
    %démodulation, retour en bande de base 
    demodule=recu .*cos(2*pi*fp*T1) - 1i*recu .*sin(2*pi*fp*T1);
    
    %filtre de récéption
    z= filter(hr,1,demodule);
    
    %echantillonage et démapping 
    xe = z(length(h1)+1:Ns:length(z));
    
    xr(1:2:nb_bits)=real(xe)<0;
    xr(2:2:nb_bits)=imag(xe)<0;
    
    TEB (k) = mean(S ~= xr);
end

%TEB simulé frequence porteuse
semilogy(EbN0dB,TEB)
xlabel('Eb/N0')
ylabel('TEB')
legend('bande de base','porteuse')