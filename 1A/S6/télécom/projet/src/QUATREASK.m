clear all;
close all;

Fe = 6000;
Te = 1/Fe;
Rb = 3000;
Tb = 1/Rb;
n=2;
M = 2^n;
Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 50000;
S = randi([0 1],nb_bits,1);
L= 6;
Ns = Fe * Ts; % Nombre d'échantillons par bits
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception

EbN0dB = [0:6];
EbN0= 10.^(EbN0dB./10);
TEB = zeros(1,length(EbN0));
figure('Name','constellation')
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
    y = filter(h1, 1, At);
    
    
    
    %bruit 
    Px = mean(abs(y).^2);
    sigma2 = (Px * Ns)/(2*log2(M)*EbN0(i));
    bruit = sqrt(sigma2) * randn(1, length(y));
    y = y+bruit;
    
    % filtre de récéption
    z = filter(hr,1,y);
   
    %echantillonage et démapping 

    xe = z(length(h1):Ns:length(z)-1);
    
     %tracé de la constellation
    nexttile 
    hist(real(xe))
    title(["Eb/N0 = " num2str(EbN0dB(i))])
    xlabel('partie réel')
    ylabel('nombre d''occuration')

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

% Tracer la DSP par rapport à l'axe des fréquences
figure('Name','DSP')
DSP1 = pwelch(y, [],[],Fe,'twosided');
axe_frequences = linspace(-Fe/2, Fe/2, length(DSP1));
semilogy(axe_frequences,fftshift(DSP1))
xlabel('Fréquence (Hz)');
ylabel('DSP');
title('tracé de la DSP par rapport a la fréquence');

%TEB théorique
TEB_th = (3/2)*qfunc(sqrt((12/15)*EbN0))/2;

figure('name','TEB th')
semilogy(EbN0dB,TEB_th,'g')
hold on
%TEB simulé
semilogy(EbN0dB,TEB(1,:),'pr')
xlabel('Eb/N0')
ylabel('TEB')
legend('TEB théorique', 'TEB simulé')