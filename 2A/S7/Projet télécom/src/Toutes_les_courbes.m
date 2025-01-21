clear all;
close all;


%% Chaine DVBS complète 
% constantes
Rb = 84.4*10^6;
Fe = Rb;
Te = 1/Fe;
Tb = 1/Rb;
n=2;
M = 2^n;

Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 188*8*100;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [-4:0.5:4];
EbN0=10.^(EbN0dB./10);
L= 8;
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception
poiscailleur = [1 1 0 1];


%codage convolutif
treillis = poly2trellis(7,[171 133]);
commcnv_plotnextstates(treillis.nextStates);

%codage de reed solomon
codage_RS = comm.RSEncoder(204,188,BitInput=true);
decode_RS = comm.RSDecoder(204,188,BitInput=true);


for k=1:length(EbN0)
    % modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);

    %Reed-Solomon
    SC = step(codage_RS,S.');
    SC = SC.';

    %entrelacement 
    octets_d = bitToOctet(SC);
    czeros= zeros(1,17*12*(12-1));
    entrelacer = convintrlv([octets_d czeros],12,17);
    SC = OctetTobit(entrelacer);

    %Poinçon + Mapping
    Code_codage = convenc(SC,treillis,poiscailleur);

    dk = 1-2*Code_codage(1:2:length(SC)*(3/2)) +1i * (1-2*Code_codage(2:2:length(SC)*(3/2)));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];

    % Filtrage
    y = filter(h1, 1, At);

    %bruit
    Px = mean(abs(y).^2);
    sigma2 = ((Px*Ns)/(2*log2(M)*EbN0(k)));

    y_et_bruit_reel = y + sqrt(sigma2)*randn(1,length(y)); % bruit réel
    recu = y_et_bruit_reel + 1i *sqrt(sigma2)*randn(1,length(y)); % bruit imaginaire




    %filtre de récéption
    z= filter(hr,1,recu);

    % Demapping + Poinçon
    xe = z(length(h1):Ns:length(z)-1);
    xr(1:2:length(SC)*(3/2))=real(xe);
    xr(2:2:length(SC)*(3/2))=imag(xe);

    S2 = vitdec(xr,treillis,5*(7-1),'trunc','unquant',poiscailleur);

    %desantrelacement
    octets_f = bitToOctet(S2);
    fin = convdeintrlv(octets_f, 12,17);
    retir = fin(17*12*11+1:end);
    code_soft = OctetTobit(retir);

    %Reed-Solomon Inverse
    code_soft_RS = step(decode_RS,code_soft.');
    code_soft_RS = code_soft_RS.';
    sauvegarde=code_soft_RS;

    TEBDVBS(k) = mean(S ~= code_soft_RS);

end
%% on enlève toutes les variables inutiles
clearvars -except TEBDVBS nb_bits Rb Fe Te Tb n M Ts Rs Ns EbN0dB EbN0 L h1 hr

%% Codage canal sans poinçonnage 
% constantes
rendement = 1/2;

treillis = poly2trellis(7,[171 133]);


for k=1:length(EbN0)

    % modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    
    Code_codage = convenc(S,treillis);

    dk = 1-2*Code_codage(1:2:nb_bits*2) +1i * (1-2*Code_codage(2:2:nb_bits*2));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % canal 
    % Filtrage
    
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


    xr(1:2:nb_bits*2)=real(xe);
    xr(2:2:nb_bits*2)=imag(xe);

    xr_h(1:2:nb_bits*2)=real(xe)<0;
    xr_h(2:2:nb_bits*2)=imag(xe)<0;

    code_soft = vitdec(xr,treillis,5*(7-1),'trunc','unquant');
    code_hard = vitdec(xr_h,treillis,5*(7-1),'trunc','hard');
    
    TEBSCo(k) = mean(S ~= code_soft);
    TEBHCo(k) = mean(S ~= code_hard);
end

%% on enlève les variables inutiles
clearvars -except TEBDVBS TEBHCo TEBSCo nb_bits Rb Fe Te Tb n M Ts Rs Ns EbN0dB EbN0 L h1 hr 

%% Codage canal avec poinçonnage 
treillis = poly2trellis(7,[171 133]);
poiscailleur = [1 1 0 1];

for k=1:length(EbN0)

    % modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    
    Code_codage = convenc(S,treillis,poiscailleur);

    dk = 1-2*Code_codage(1:2:nb_bits*(3/2)) +1i * (1-2*Code_codage(2:2:nb_bits*(3/2)));
    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    % canal 
    % Filtrage
    
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


    xr(1:2:nb_bits*(3/2))=real(xe);
    xr(2:2:nb_bits*(3/2))=imag(xe);

    code_soft = vitdec(xr,treillis,5*(7-1),'trunc','unquant',poiscailleur);
    
    TEBSCoP(k) = mean(S ~= code_soft);
end

%% on enlève les variables inutiles
clearvars -except TEBDVBS TEBHCo TEBSCo TEBSCoP nb_bits Rb Fe Te Tb n M Ts Rs Ns EbN0dB EbN0 L h1 hr 

%% Codage avec RS en plus

%codage de reed solomon
codage_RS = comm.RSEncoder(204,188,BitInput=true);
decode_RS = comm.RSDecoder(204,188,BitInput=true);


%codage convolutif
treillis = poly2trellis(7,[171 133]);
poiscailleur = [1 1 0 1];

for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    
    S1 = step(codage_RS,S.');
    S1 = S1.';

    Code_codage = convenc(S1,treillis,poiscailleur);

    dk = 1-2*Code_codage(1:2:length(S1)*(3/2)) +1i * (1-2*Code_codage(2:2:length(S1)*(3/2)));

    At = [kron(dk, [1, zeros(1, Ns-1)]) zeros(1,length(h1))];
    
    %% canal 
    % Filtrage
    
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


    xr(1:2:length(S1)*(3/2))=real(xe);
    xr(2:2:length(S1)*(3/2))=imag(xe);

    xr_h(1:2:length(S1)*(3/2))=real(xe)<0;
    xr_h(2:2:length(S1)*(3/2))=imag(xe)<0;

    code_soft = vitdec(xr,treillis,5*(7-1),'trunc','unquant',poiscailleur);
    code_soft_RS = step(decode_RS,code_soft.');
    code_soft_RS = code_soft_RS.';

    TEBRS(k) = mean(S ~= code_soft_RS);
end

%% courbes 

a = figure('Name','différents TEB');


% on nomme les axes
xlabel('Eb/N0 (dB)')
ylabel('TEB')

%TEB simulé avec hard décodage
semilogy(EbN0dB,TEBHCo,'-o')
hold on


% TEB simulé avec soft décodage
semilogy(EbN0dB,TEBSCo,'-o')
hold on


% TEB simulé avec soft décodage et poinçonnage
semilogy(EbN0dB,TEBSCoP,'-o')
hold on


% TEB simulé avec soft décodage et poinçonnage et RS
semilogy(EbN0dB,TEBRS,'-o')
hold on


% TEB simulé avec toute la chaine DVBS
semilogy(EbN0dB,TEBDVBS,'-o')
hold on


%TEB théorique
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'g')
legend('TEB Codage canal hard','TEB Codage canal soft','TEB codage canal soft avec poiçonage','TEB codage canal soft avec poissonage et RS','TEB de la chaine DVBS', 'TEB théorique')
grid on


lines = findall(a, 'Type', 'Line');
set(lines, 'LineWidth', 1.5);