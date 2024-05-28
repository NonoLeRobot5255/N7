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

EbN0dB = 100;
EbN0=10.^(EbN0dB./10);
L= 6;
h1 = rcosdesign(0.35,L,Ns); % Reponse impulsionnelle du filtre
hr = fliplr(h1);


%% Modulateur
S = randi([0 1],1,nb_bits);
S2 = reshape(S',2,nb_bits/2);
S2E = [1, nb_bits/2];
Choix = [0 1; 3 2];
for j=1:size(S2,2)
    S2E(j) = Choix(S2(1,j)+1,S2(2,j)+1);
end
x = pammod(S2E,4,0,'gray');
At = [kron(x, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];


% filtre 
y = filter(h1, 1, At);

T1 = ([0:length(y)-1] * Te);

%bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0));
    
    recu=y+sqrt(sigma2)*randn(1,length(y));
    
    
    %filtre de récéption
    z= filter(hr,1,recu);

    
    %echantillonage et démapping 
    xe = z(length(h1)+1:Ns:length(z));

    %tracé de la constellation
    
    
    xr_temp = pamdemod(xe,4,0,'gray');
    xr = [];
    for j=1:length(S)/2
    if xr_temp(j)== 0
        xr = [xr 0 0];
    elseif xr_temp(j)== 1
        xr = [xr 0 1];
    elseif xr_temp(j)== 2
        xr = [xr 1 1];
    else
        xr = [xr 1 0];
    end
    
end
    
    TEB  = mean(S ~= xr)
    