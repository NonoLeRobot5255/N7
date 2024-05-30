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
nb_bits = 16;
S = randi([0 1],1,nb_bits);
SNR = 200;
L= 8;

%% modulateur :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons par bits
dk = 1-2*S(1:2:nb_bits) +1i * (1-2*S(2:2:nb_bits));
At = [kron(dk, [1, zeros(1, Ns-1+L*Ns)])];

% Filtre
% Echelle temporelle
h1 = rcosdesign(0.35,L,Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);
T1 = ([0:length(y)-1] * Te);

%filtre de réception
z= filter(h1,1,y);


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


%porteuse
p = real(y) .*cos(2*pi*fp*T1) - imag(y) .*sin(2*pi*fp*T1);

% Tracer la DSP par rapport à l'axe des fréquences
figure('Name','DSP')
DSP1 = pwelch(p, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP1));
nexttile
semilogy(axe_frequences,fftshift(DSP1))
xlabel('Fréquence (Hz)');
ylabel('DSP');
title('tracé de la DSP par rapport a la fréquence');

%bruit
Px = mean(abs(p).^2);
sigma2 = ((Px * Ns)/(2*log2(M)*SNR));


%filtre de récéption
hr = fliplr(h1);
z= filter(hr,1,y);

%réponse global
r = conv(h1,hr);
figure('Name','réponse impulsionelle globale')
plot (r)

%instant optimal


%diagramme de l'oeil
eyediagram(z,2*Ns,2*Ns)

%echantillonage
xe = z(length(h1):Ns:length(h1)+Ns*length(dk));
xr = [];
for c=1:size(xe,2)-1
    if (real(xe(c))>0 && imag(xe(c))>0)
        xr=[xr 0 0];
    elseif (real(xe(c))<=0 && imag(xe(c))>0)
        xr =[xr 0 1];
    elseif (real(xe(c))<=0 && imag(xe(c))<=0)
        xr =[xr 1 1];
    else 
        xr =[xr 1 0];
    end
end
 
TEB = mean(S ~= xr)