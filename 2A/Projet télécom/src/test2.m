
%%% III.2 %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

close all
clear all



Nbit = 188*8*10; %Nombre de bits
BW = 50000000; %Bande passante
alpha = 0.35; %Facteur de Roll-Off
Rs = BW/(1+alpha); %Debit binaire
Fe = 100000000; %Fe Ã  100MHz (cf norme)
Te = 1/Fe; %PÃ©riode d'Ã©chantillonnage
Tb = 1/Rs; %PÃ©riode binaire
M = 4; %Ordre de modulation

Ts = log2(M)*Tb; % PÃ©riode symbole



%% GÃ©nÃ©ration d'un signal binaire

binRS = randi([0,1],1,Nbit);


%% Codage RS(204,188)

encodeur = comm.RSEncoder(204,188,'BitInput',true);
bincode = encodeur(binRS'); 

%utilisÃ© pour le dÃ©codage
decodeur = comm.RSDecoder(204,188,'BitInput',true);



%% Entrelaceur


octets = bitToOctet(bincode)';

retard_entrelaceur = zeros(1,17*12*11); % On introduit le retard liÃ© Ã  l'entrelaceur
octets = [octets retard_entrelaceur];

entrelace = convintrlv(octets,12,17); % On entrelace les octets


entrelace_bits = OctetTobit(entrelace); % On transforme les octets entrelacÃ©s en bits
entrelace_bits = entrelace_bits';


%% Codage convolutif du signal binaire
polynome = [171 133];
LongContrainte = 7;
poinconnage = [1 1 0 1];
treillis = poly2trellis(LongContrainte,polynome);
commcnv_plotnextstates(treillis.nextStates);

sortieRS = convenc(bincode',treillis,poinconnage);
sortie_entrelace = convenc(entrelace_bits,treillis,poinconnage)';

%% Mapping

a_k = 2*sortieRS(1:2:end) -1;
b_k = 2*sortieRS(2:2:end) -1;
mappingRS = -(a_k + 1i*b_k); % On a mis un - pour coller avec la norme 

a_k = 2*sortie_entrelace(1:2:end) -1;
b_k = 2*sortie_entrelace(2:2:end) -1;
mapping = -(a_k + 1i*b_k);

%% SurÃ©chantillonageecodeur = comm.RSDecoder(204,188,'BitInput',true);
% L'implÃ©mentation d'un filtre de mise en forme en racine de cosinus
% surÃ©levÃ© crÃ©Ã© un retard sur le signal. On le compense en
% surÃ©chantillonnant le signal.

SPS = 6 ; 
peigne = zeros(1,SPS);
peigne(1) = 1;  
x = kron(mapping,peigne);
xRS = kron(mappingRS,peigne);

%% Filtrage de mise en forme

SPAN = 10; %Facteur apportant un TEB optimal
h = rcosdesign(alpha,SPAN,SPS);
retard = SPAN*SPS/2; %retard minimal introduit par le filtre

y = filter(h,1,[x ,zeros(1,retard)]);
Xe = y(retard+1:end);

yRS = filter(h,1,[xRS, zeros(1,retard)]);
XeRS = yRS(retard+1:end);
%% Passage dans un canal AWGN
EbN0dB = -1:0.25:1;
TEBRS = zeros(length(EbN0dB),1);
TEBpoinconne = zeros(length(EbN0dB),1);

for i=1:length(TEBRS)
    nberreurentrelace = 0;
    nberreurRS = 0;
    while (nberreurRS < 10)
        %Puissance du signal transmis
        Px = mean(abs(XeRS).^2);

        %Racine de la puissance du bruit
        sigma_n = Px*SPS/(2*log2(M)*10^(EbN0dB(i)/10));

        %Calcul du bruit
        bruitI = sqrt(sigma_n) * randn(1,length(XeRS));     % Introduction du bruit rÃ©el et imaginaire
        bruitQ = sqrt(sigma_n) * randn(1,length(XeRS));

        %Ajout du bruit
        r = XeRS + bruitI + 1i*bruitQ;

        %% DÃ©modulation  

        hr = fliplr(h); %filtre adaptÃ©
        z = filter(hr,1,[r ,zeros(1,retard)]);
        z = z(retard+1:end);

        %% Instant d'Ã©chantillonage

        n0 = SPS;
        dm = z(1:SPS:end);


        %% DÃ©cisions
        am = -(real(dm));
        bm = -(imag(dm));

        %% Demapping
        xm = zeros(1,length(sortieRS));
        xm(1:2:end) = -am;
        xm(2:2:end) = -bm;


        %% DÃ©codage en utilisant l'algorithme de Viterbi, codage soft.

        TraceBack = 30;
        xmdecodepoinconneRS = vitdec(xm,treillis,TraceBack,'trunc','unquant',poinconnage);


        %% DÃ©codage RS

        bindecodeRS = decodeur(xmdecodepoinconneRS');

        %% Calcul du TEB
        nberreurRS = nberreurRS + sum(bindecodeRS~=binRS');
        TEB_calcRS = length(find((bindecodeRS-binRS') ~= 0))/length(binRS);
    end
    while (nberreurentrelace < 10)
        %Puissance du signal transmis
        Px = mean(abs(Xe).^2);

        %Racine de la puissance du bruit
        sigma_n = Px*SPS/(2*log2(M)*10^(EbN0dB(i)/10));

        %Calcul du bruit
        bruitI = sqrt(sigma_n) * randn(1,length(Xe));       % Introduction du bruit rÃ©el et imaginaire
        bruitQ = sqrt(sigma_n) * randn(1,length(Xe));

        %Ajout du bruit
        r = Xe + bruitI + 1i*bruitQ;
        % r = Xe;
        %% DÃ©modulation  
        hr = fliplr(h); %filtre adaptÃ©
        z = filter(hr,1,[r ,zeros(1,retard)]);
        z = z(retard+1:end);

        %% Instant d'Ã©chantillonage
        n0 = SPS;
        dm = z(1:SPS:end);


        %% DÃ©cisions
        am = -(real(dm));
        bm = -(imag(dm));

        %% Demapping
        xm = zeros(1,length(sortie_entrelace));
        xm(1:2:end) = -am;
        xm(2:2:end) = -bm;


        %% DÃ©codage en utilisant l'algorithme de Viterbi, codage soft.

        TraceBack = 30;
        xmdecodeentrelace = vitdec(xm,treillis,TraceBack,'trunc','unquant',poinconnage);

        %% Desentrelacement

        octets_desentrelace = bitToOctet(xmdecodeentrelace);

        de_entrelace = convdeintrlv(octets_desentrelace,12,17); 
        de_entrelace = [de_entrelace(17*12*11+1:end)];
        

        de_entrelace_bits = OctetTobit(de_entrelace);
        de_entrelace_bits = de_entrelace_bits';

        %% DÃ©codage RS

        bindecode = decodeur(de_entrelace_bits);

        %% Calcul du TEB
        nberreurentrelace = nberreurentrelace + sum(bindecode~=binRS');
        TEB_calcentrelace = length(find((bindecode-binRS') ~= 0))/length(binRS);
    end
    
    TEBentrelace(i) = TEB_calcentrelace;
    TEBRS(i) = TEB_calcRS;
end


%% TracÃ© de la courbe TEB
TEB_th = 2*qfunc(sqrt(2*log2(M)*10.^(EbN0dB/10))*sin(pi/M))/log2(M); % TEB thÃ©orique QPSK;
figure
semilogy(EbN0dB,TEBentrelace,'b-');
hold on
semilogy(EbN0dB,TEBRS,'g-');
hold on
semilogy(EbN0dB,TEB_th,'r-');
grid on;
legend('TEB simulÃ© avec entrelacement','TEB simulÃ© avec poinconnage et codage RS','TEB thÃ©orique sans codage');
xlabel('Eb/N0 (dB)')
ylabel('TEB')
title('TracÃ© des TEB');