clear all;
close all;

%% QPSK bande de base

%% Constantes
rendement = 1/2;
Rb = 84.4 * 10^6; % Débit binaire en bits par seconde
Fe = Rb; % Fréquence d'échantillonnage 
Te = 1 / Fe; % Période d'échantillonnage
Tb = 1 / Rb; % Durée d'un bit
n = 2; % Nombre de bits par symbole
M = 2^n; % Ordre de la modulation

Ts = log2(M)*Tb; % Durée d'un symbole
Rs = Rb / log2(M); % Débit symbole
nb_bits = 100000 ; % Nombre total de bits à simuler
Ns = Fe * Ts; % Nombre d'échantillons par symbole

EbN0dB = [-4:4]; % Rapport signal sur bruit en dB
EbN0 = 10.^(EbN0dB / 10); % Rapport signal sur bruit linéaire
L = 8; % Longueur du filtre en nombre de symboles
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception
poinconneur = [1 1 0 1];

%codage convolutif
treillis = poly2trellis(7,[171 133]);
commcnv_plotnextstates(treillis.nextStates);

%% CHAINE DE TRANSMISSION
for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    
    Code_codage = convenc(S,treillis,poinconneur);

    dk = 1-2*Code_codage(1:2:nb_bits*(3/2)) +1i * (1-2*Code_codage(2:2:nb_bits*(3/2)));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    %% canal 
    % Filtrage de mise en forme
    y = filter(h1, 1, At);
    T1 = ([0:length(y)-1] * Te);
   
    % Ajout de bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));
    y_et_bruit_reel = y + sqrt(sigma2)*randn(1,length(y)); % bruit réel
    recu = y_et_bruit_reel + 1i *sqrt(sigma2)*randn(1,length(y)); % bruit imaginaire
    
    
    % Filtre de récéption
    z= filter(hr,1,recu);

    
    % Demapping + Dépoinçonnage 
    xe = z(length(h1):Ns:length(z)-1);
    xr(1:2:nb_bits*(3/2))=real(xe);
    xr(2:2:nb_bits*(3/2))=imag(xe);

    code_soft = vitdec(xr,treillis,5*(7-1),'trunc','unquant',poinconneur);
    
    % Calcul du TEB
    TEB1(k) = mean(S ~= code_soft);
end

%% Trace des courbes
figure
%TEB simulé avec soft décodage
semilogy(EbN0dB,TEB1)
xlabel('Eb/N0 (dB)')
ylabel('TEB')
hold on
%TEB théorique
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'g')
legend('TEB avec codage et décodage soft et poinçonnage', 'TEB théorique')
grid on
