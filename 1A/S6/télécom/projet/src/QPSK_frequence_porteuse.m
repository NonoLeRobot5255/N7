clear all;
close all;

Fe = 24000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=2;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
fp = 2000;
nb_bits = 10000;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [0:6];
EbN0=10.^(EbN0dB./10);
L= 8;
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

%partie réel 
figure('Name','partie réel')
plot(real(z),'LineWidth',3)
hold on
stem(1:Ns:Ns*nb_bits/2,real(dk),'rp','LineWidth',3)
stem(length(h1):Ns:length(z),z(length(h1):Ns:length(z)),'dg','LineWidth',3)
xlabel('Temps (échantillons)')
ylabel('Amplitude')
title('Partie Réelle du Signal après Filtrage')
legend('Signal Filtré','Symboles Transmis','Symboles Reçus','Location','best')


%partie imaginaire 
figure('Name','partie imaginaire')
plot(imag(z),'LineWidth',3)
hold on
stem(1:Ns:Ns*nb_bits/2,imag(dk),'rp','LineWidth',3)
stem(length(h1):Ns:length(z),imag(z(length(h1):Ns:length(z))),'dg','LineWidth',3)
xlabel('Temps (échantillons)')
ylabel('Amplitude')
title('Partie Imagi du Signal après Filtrage')
legend('Signal Filtré','Symboles Transmis','Symboles Reçus','Location','best')

% Tracer la DSP par rapport à l'axe des fréquences
figure('Name','DSP')
DSP1 = pwelch(p, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP1));
nexttile
semilogy(axe_frequences,fftshift(DSP1))
xlabel('Fréquence (Hz)');
ylabel('DSP');
title('tracé de la DSP par rapport a la fréquence');

figure
%TEB théorique
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'g')
hold on
%TEB simulé
semilogy(EbN0dB,TEB,'pr')
xlabel('EB/N0')
ylabel('TEB')
legend('TEB théorique','TEB simulé')