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
nb_bits = 10000 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [100];
EbN0=10.^(EbN0dB./10);
L= 6;
h1 = rcosdesign(0.35,L,Ns); % Reponse impulsionnelle du filtre
hr = fliplr(h1);

for k=1:length(EbN0)
%% Modulateur
S = randi([0 1],1,nb_bits);
x = pammod(S,4);
At = [kron(x, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];


% filtre 
y = filter(h1, 1, At);

T1 = ([0:length(y)-1] * Te);

%bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));
    
    recu=y+sqrt(sigma2)*randn(1,length(y));
    
    
    %filtre de récéption
    z= filter(hr,1,recu);

    
    %echantillonage et démapping 
    xe = z(length(h1)+1:Ns:length(z));


    %tracé de la constellation
    figure('Name','constellation')
    plot(xe,zeros(1,length(xe)),'linestyle','none','marker','o')
    
    xr = pamdemod(xe,4);
    
    TEB(k)  = mean(S ~= xr);

end

figure
%TEB théorique
semilogy(EbN0dB,(3/2)*qfunc(sqrt((12/15)*EbN0))/2,'g')
hold on
%TEB simulé
semilogy(EbN0dB,TEB,'pr')