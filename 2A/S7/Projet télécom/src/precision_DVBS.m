clear all;
close all;


%% Constantes
Rb = 84.4 * 10^6; % Débit binaire en bits par seconde
Fe = Rb; % Fréquence d'échantillonnage 
Te = 1 / Fe; % Période d'échantillonnage
Tb = 1 / Rb; % Durée d'un bit
n = 2; % Nombre de bits par symbole
M = 2^n; % Ordre de la modulation 

Ts = log2(M) * Tb; % Durée d'un symbole
Rs = Rb / log2(M); % Débit symbole
nb_bits = 188 * 8 * 10; % Nombre total de bits à simuler
Ns = Fe * Ts; % Nombre d'échantillons par symbole

%Precision 
Ne=0; % Nombre d'erreurs
EbN0dB = 10; % Rapport signal sur bruit en dB
EbN0 = 10*log10(EbN0dB); % Rapport signal sur bruit linéaire


k=0; % Nombre d'itérations
L = 8; % Longueur du filtre en nombre de symboles
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception
poinconneur = [1 1 0 1]; % Poinçonnage pour le codage convolutif


% Codage convolutif
treillis = poly2trellis(7,[171 133]);
commcnv_plotnextstates(treillis.nextStates);

% Codage de Reed-Solomon
codage_RS = comm.RSEncoder(204,188,BitInput=true);
decode_RS = comm.RSDecoder(204,188,BitInput=true);

%% PRECISION
while Ne<4 && k<100000
    k=k+1;
    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    
    % Codage Reed-Solomon
    S1 = step(codage_RS,S.');
    S1 = S1.';
    
    % Entrelacement 
    octets_d = bitToOctet(S1);
    czeros= zeros(1,17*12*(12-1));
    entrelacer = convintrlv([octets_d czeros],12,17);
    S1 = OctetTobit(entrelacer);
    
    % Codage convolutif + Mapping
    Code_codage = convenc(S1,treillis,poinconneur);
    
    dk = 1-2*Code_codage(1:2:length(S1)*(3/2)) +1i * (1-2*Code_codage(2:2:length(S1)*(3/2)));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % Filtrage de mise en forme
    y = filter(h1, 1, At);
    
    % Ajout de bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0));
    
    y_et_bruit_reel = y + sqrt(sigma2)*randn(1,length(y)); % bruit réel
    recu = y_et_bruit_reel + 1i *sqrt(sigma2)*randn(1,length(y)); % bruit imaginaire
    
    % Filtre de récéption
    z= filter(hr,1,recu);
    
    % Demapping + Dépoinçonnage
    xe = z(length(h1):Ns:length(z)-1);
    xr(1:2:length(S1)*(3/2))=real(xe);
    xr(2:2:length(S1)*(3/2))=imag(xe);
    
    S2 = vitdec(xr,treillis,5*(7-1),'trunc','unquant',poinconneur);
    
    % Desantrelacement
    octets_f = bitToOctet(S2);
    fin = convdeintrlv(octets_f, 12,17);
    retir = fin(17*12*11+1:end);
    code_soft = OctetTobit(retir);
    
    % Décodage Reed-Solomon inverse
    code_soft_RS = step(decode_RS,code_soft.');
    code_soft_RS = code_soft_RS.';
    
    Ne = Ne + sum(code_soft_RS ~= S);

end


prec = (1/Ne)^0.5;
TEB_precision = Ne/(k*10000);