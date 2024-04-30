clear all;
close all;

Fe = 24000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=1;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 10000;
S = randi([0 1],nb_bits,1);

SNRdB = 0.1:0.1:8;
SNR=10.^(SNRdB./10);
TEB2 = zeros(1,length(SNR));
for i=1:size(SNR,2)

    %% modulateur 1 :
    % Mapping
    
    Ns = Fe * Ts; % Nombre d'échantillons! par bits
    
    SE = (2*S - 1)';
    At = kron(SE, [1 zeros(1, Ns-1)]);
    
    % Filtre
    T1 = 0:Te:(nb_bits*Ns-1)*Te; % Echelle temporelle
    h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
    y = filter(h1, 1, At);
    
    
       %bruit 
    Px = mean(abs(y).^2);
    sigma2 = ((Px * Ns)/(2*log2(M)*SNR(i)));
    bruit = sqrt(sigma2) * randn(1, length(y));
    y = y+bruit;  
   
    
    % filtre réception 
    hr = ones(1,Ns);
    y = filter(hr,1,y);
    
    % réponse globale impulsion
    
    g = conv(h1,h1);
    t_g = linspace(0,2*Ns,length(g));
    
    N0=floor(Ts*Fe);
    xe = y(N0:Ns:length(y));
    xr = zeros(1,length(S));
    xr(xe>0)=1;
    xr(xe<0)=0;
    
    
    TEB2(i) = mean(S' ~= xr);
end


figure('name','TEB 1 vs 2')
semilogy(SNRdB,TEB2(1,:));
legend('chaine 1')
hold on


SNRdb = [0.1:0.1:8];
SNR= 10.^(SNRdb./10);
TEB = zeros(1,length(SNR));
for i=1:size(SNR,2)

   %% modulateur 2 :
% Mapping

Ns = Fe * Ts; % Nombre d'échantillons! par bits

SE = (2*S - 1)';
At = kron(SE, [1 zeros(1, Ns-1)]);

% Filtre
T1 = 0:Te:(nb_bits*Ns-1)*Te; % Echelle temporelle
h1 = ones(1, Ns); % Reponse impulsionnelle du filtre
y = filter(h1, 1, At);



%bruit 
Px = mean(abs(y).^2);
sigma2 = (Px * Ns)/(2*log2(M)*SNR(i));
bruit = sqrt(sigma2) * randn(1, length(y));
y = y+bruit;

% filtre récéption
hr = ones(1,Ns/2);
y = filter(hr,1,y);

g = conv(h1,hr);
t_g = linspace(0,2*Ns,length(g));

% Diagramme de l'oeil
oeil = reshape(y,Ns,length(y)/Ns);
to= linspace(0,Ns,size(oeil,1));

N0=floor(Ts*Fe);
xe = y(N0:Ns:length(y));
xr = zeros(1,length(S));
xr(xe>0)=1;
xr(xe<0)=0;


TEB(i) = mean(S' ~= xr);
end



semilogy(SNRdb,TEB(1,:))
legend('chaine 1','chaine 2')