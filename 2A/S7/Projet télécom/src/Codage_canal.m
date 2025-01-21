clear all;
close all;

%% QPSK bande de base

%% constantes
rendement = 1/2;
% B = 1.35 *Rs = 54 * 10^6;
Rb = 84.4*10^6;
Fe = Rb;
Te = 1/Fe;
Tb = 1/Rb;
n=2;
M = 2^n;

Ts = log2(M)*Tb;
Rs = Rb/log2(M);
nb_bits = 188*8*100 ;
Ns = Fe * Ts; % Nombre d'échantillons par bits

EbN0dB = [-4:0.5:4];
EbN0=10.^(EbN0dB./10);
L= 8;
h1 = rcosdesign(0.35,L,Ns); % filtre de mise en forme
hr = fliplr(h1); % filtre de réception

treillis = poly2trellis(7,[171 133]);
commcnv_plotnextstates(treillis.nextStates);
for k=1:length(EbN0)

    %% modulateur :
    % Mapping
    S = randi([0 1],1,nb_bits);
    
    Code_codage = convenc(S,treillis);

    dk = 1-2*Code_codage(1:2:nb_bits*2) +1i * (1-2*Code_codage(2:2:nb_bits*2));
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


    xr(1:2:nb_bits*2)=real(xe);
    xr(2:2:nb_bits*2)=imag(xe);

    xr_h(1:2:nb_bits*2)=real(xe)<0;
    xr_h(2:2:nb_bits*2)=imag(xe)<0;

    code_soft = vitdec(xr,treillis,5*(7-1),'trunc','unquant');
    code_hard = vitdec(xr_h,treillis,5*(7-1),'trunc','hard');
    
    TEB1(k) = mean(S ~= code_soft);
    TEB2(k) = mean(S ~= code_hard);
end


figure
%TEB simulé avec soft décodage
semilogy(EbN0dB,TEB1)
xlabel('Eb/N0 (dB)')
ylabel('TEB')
hold on
%TEB simulé avec hard décodage
semilogy(EbN0dB,TEB2)
hold on
%TEB théorique
semilogy(EbN0dB,qfunc(sqrt(2*EbN0)),'g')
legend('TEB avec codage et décodage soft','TEB avec codage et décodage hard', 'TEB théorique')
grid on
