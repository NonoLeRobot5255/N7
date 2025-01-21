clear all;
close all;


%% constantes
Rb = 84.4*10^6;
Fe = Rb;
Te = 1/Fe;
Tb = 1/Rb;
n=2;
M = 2^n;

Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 188*8*10;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [-4:0.25:4];
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
    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    S(1)=1;
    
    %Reed-Solomon
    S1 = step(codage_RS,S.');
    S1 = S1.';
    
    %entrelacement 
    octets_d = bitToOctet(S1);
    czeros= zeros(1,17*12*(12-1));
    entrelacer = convintrlv([octets_d czeros],12,17);
    S1 = OctetTobit(entrelacer);
    
    %Poinçon + Mapping
    Code_codage = convenc(S1,treillis,poiscailleur);
    
    dk = 1-2*Code_codage(1:2:length(S1)*(3/2)) +1i * (1-2*Code_codage(2:2:length(S1)*(3/2)));
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
    xr(1:2:length(S1)*(3/2))=real(xe);
    xr(2:2:length(S1)*(3/2))=imag(xe);
    
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
    
    TEB1(k) = mean(S ~= code_soft_RS);

end



figure
%TEB simulé avec soft décodage
semilogy(EbN0dB,TEB1)
xlabel('Eb/N0 (dB)')
ylabel('TEB')
hold on
%TEB simulé avec hard décodage
% semilogy(EbN0dB,TEB2)
% hold on
%TEB théorique
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'g')
legend('TEB avec codage et décodage soft et poinçonnage', 'TEB théorique')
grid on