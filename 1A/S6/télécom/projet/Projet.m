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
nb_bits = 30;
S = randi([0 1],1,nb_bits);



%% modulateur :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons! par bits
dk = 1-2*S(1:2:nb_bits) +1i * (1-2*S(2:2:nb_bits));
At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,4*Ns+1)];

% Filtre
 % Echelle temporelle
h1 = rcosdesign(0.35,4,Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);
T1 = ([0:length(y)-1] * Te)';
z= filter(h1,1,y);


%partie réel 
figure('Name','partie réel')
plot(real(z),'LineWidth',3)
hold on
stem(1:Ns:Ns*nb_bits/2,real(dk),'rp','LineWidth',3)
stem(length(h1):Ns:length(z),z(length(h1):Ns:length(z)),'dg','LineWidth',3)


%partie imaginaire 
figure('Name','partie imaginaire')
plot(imag(z),'LineWidth',3)
hold on
stem(1:Ns:Ns*nb_bits/2,imag(dk),'rp','LineWidth',3)
stem(length(h1):Ns:length(z),imag(z(length(h1):Ns:length(z))),'dg','LineWidth',3)


%porteuse
y = real(y) .*cos(2*pi*fp*T1) -imag(y) .*sin(2*pi*fp*T1);